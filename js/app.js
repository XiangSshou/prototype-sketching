/**
 * ============================================
 * 原型画布 · 主程序
 * --------------------------------------------
 * - 纯前端：数据保存在 IndexedDB（无后端）
 * - 无限画布：多页面画板同屏展示，元素坐标相对于所属页面（局部坐标）
 * - 全局相机 project.camera；连线：锚点接起终点（线连中心），双击沿唯一出边跳转
 * - Ctrl+Z：撤销上一项对项目的修改（快照栈，仅存于内存）
 * ============================================
 */

(function () {
  'use strict';

  // ---------- 常量：存储与防抖 ----------
  /** IndexedDB 数据库名 */
  const DB_NAME = 'prototype-canvas-db';
  /** 对象仓库名（单 key 存整个项目 JSON） */
  const STORE_NAME = 'projects';
  /** 固定 key，当前始终只维护一个项目（后续可扩展多项目列表） */
  const PROJECT_KEY = 'current';
  /** 自动保存防抖间隔（毫秒）：避免每次鼠标移动都写盘 */
  const SAVE_DEBOUNCE_MS = 450;

  /** 默认设计分辨率（可在侧栏修改） */
  const DEFAULT_WIDTH = 1920;
  const DEFAULT_HEIGHT = 1080;

  /** 撤销栈最大深度（避免长时间编辑占用过多内存） */
  const MAX_UNDO = 50;

  /** 矩形 / 椭圆 / 直线 / 手绘共用的默认描边色与线宽（与手绘视觉一致） */
  const DEFAULT_DRAW_STROKE = '#c8c8d0';
  const DEFAULT_DRAW_STROKE_WIDTH = 1.5;

  /** 新建画板与已有画板之间的水平间距（世界坐标） */
  const PAGE_GAP = 80;

  /** 对齐网格：在「项目默认宽高」基础上每轴多加的像素（世界坐标步长的一部分） */
  const GRID_ALIGN_EXTRA = 200;

  /** 选择穿透：与上一次点击屏幕距离小于此值（像素）视为「同一点」连击 */
  const PICK_CYCLE_RADIUS_PX = 10;

  /** 连线工具：锚点命中半径（屏幕像素）；无效目标为深红高亮 */
  const CONNECT_ANCHOR_RADIUS_PX = 9;

  // ---------- DOM 引用 ----------
  const canvas = document.getElementById('canvas');
  const ctx = canvas.getContext('2d');
  const textEditor = document.getElementById('text-editor');

  const elProjectName = document.getElementById('project-name');
  const elProjectWidth = document.getElementById('project-width');
  const elProjectHeight = document.getElementById('project-height');
  const elShowFrame = document.getElementById('show-frame');
  const elPageList = document.getElementById('page-list');
  const elSaveStatus = document.getElementById('save-status');
  const elBtnAddPage = document.getElementById('btn-add-page');
  const elBtnExport = document.getElementById('btn-export');
  const elBtnImport = document.getElementById('btn-import');
  const elImportFile = document.getElementById('import-file');
  const elBtnDelete = document.getElementById('btn-delete');
  const elBtnAlignGrid = document.getElementById('btn-align-grid');
  const elPageWidth = document.getElementById('page-width');
  const elPageHeight = document.getElementById('page-height');
  const toolButtons = document.querySelectorAll('.tool');
  const elCanvasHint = document.getElementById('canvas-hint');

  // ---------- 运行时状态 ----------
  /** @type {'select'|'rect'|'ellipse'|'line'|'draw'|'text'|'connect'} */
  let currentTool = 'select';

  /** 当前激活页面 id */
  let activePageId = '';

  /**
   * 选中元素：同一页面内的节点 id（连线不作为选中主体）
   * @type {string|null}
   */
  let selectedNodeId = null;

  /** 相机：scale 为缩放倍数；tx,ty 为画布 CSS 像素偏移（世界坐标乘 scale 后加上平移得到屏幕坐标） */
  let camera = { tx: 0, ty: 0, scale: 1 };

  /** 空格按住时进入平移模式 */
  let spaceDown = false;

  /** 连线工具：第一次点击记录的端点 */
  let connectAnchor = null;

  /** 矩形/椭圆：拖拽起点（当前页面局部坐标） */
  let dragLocalStart = null;

  /** 手绘：当前笔触所在页面 id */
  let drawStrokePageId = '';

  /** 手绘：当前笔触点列（页面局部坐标） */
  let drawPoints = [];

  /** Ctrl/⌘ 合并：下一笔（按下时仍按住）将并入的路径 id 与其所在页 id */
  let drawCtrlMergePathId = '';
  let drawCtrlMergePageId = '';
  /** 当前这一笔在 pointerdown 时是否按下了 Ctrl 或 ⌘ */
  let drawStrokeCtrlDown = false;

  /** 直线工具：两点模式的第一点 { pageId, x, y } */
  let lineFirstPoint = null;

  /** 同一点连续点击穿透选择：上次屏幕坐标与 cycle 下标 */
  let lastPickScreenX = NaN;
  let lastPickScreenY = NaN;
  let pickCycleIndex = 0;

  /**
   * 当前处于「选中页面画板」状态（穿透选择到 page 或左侧点了页面）时记录该页 id，
   * 便于在画板空白处直接拖拽移动页面（无需按住 Alt）。
   */
  let pageFrameSelectedId = null;

  /** 移动选中元素时的偏移 */
  let moveGrabOffset = null;

  /** 自动保存定时器 */
  let saveTimer = null;

  /** 相机动画：目标 tx,ty,scale 与起始值 */
  let cameraAnim = null;

  /**
   * 撤销历史：每项为「修改前」的完整项目深拷贝。
   * Ctrl+Z 弹出栈顶并赋回 project。
   */
  let undoStack = [];

  /** 为 true 时表示正在 restore，禁止 pushUndo（防止撤销操作本身污染栈） */
  let undoRestoring = false;

  /** 项目名称输入框：仅在首次输入时压一次快照，避免每个字符一步撤销 */
  let projectNameUndoPrimed = true;

  /**
   * 完整项目数据（可序列化）
   * @type {ProjectState}
   */
  let project = createEmptyProject();

  /**
   * @typedef {Object} Camera
   * @property {number} tx
   * @property {number} ty
   * @property {number} scale
   */

  /**
   * @typedef {Object} ElementNode
   * @property {string} id
   * @property {'rect'|'ellipse'|'line'|'path'|'text'} type
   * @property {number} x
   * @property {number} y
   * @property {number} [w]
   * @property {number} [h]
   * @property {number} [x2]
   * @property {number} [y2]
   * @property {([number,number]|null)[]} [points]  null 表示子路径断开（Ctrl 合并多笔）
   * @property {string} [text]
   * @property {string} [fill]
   * @property {string} [stroke]
   * @property {number} [strokeWidth]
   * @property {number} [fontSize]
   */

  /**
   * 连线端点：nodeId 为 null 表示「整页」，几何中心取页面中心
   * @typedef {Object} EdgeEndpoint
   * @property {string} pageId
   * @property {string|null} nodeId
   */

  /**
   * @typedef {Object} Edge
   * @property {string} id
   * @property {EdgeEndpoint} source
   * @property {EdgeEndpoint} target
   */

  /**
   * 页面画板：在世界坐标系中的矩形区域，子元素使用相对画板左上角的局部坐标
   * @typedef {Object} Page
   * @property {string} id
   * @property {string} name
   * @property {number} x
   * @property {number} y
   * @property {number} width
   * @property {number} height
   * @property {ElementNode[]} elements
   */

  /**
   * @typedef {Object} ProjectState
   * @property {string} name
   * @property {number} designWidth
   * @property {number} designHeight
   * @property {boolean} showFrame
   * @property {Camera} camera
   * @property {string} activePageId
   * @property {Page[]} pages
   * @property {Edge[]} edges
   */

  // ============================================
  // 工具函数：ID / 深拷贝 / 空项目
  // ============================================

  function newId() {
    // crypto.randomUUID 在现代浏览器可用；降级为时间戳随机串
    if (crypto.randomUUID) return crypto.randomUUID();
    return 'id-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 9);
  }

  function createEmptyProject() {
    const pageId = newId();
    return {
      name: '未命名项目',
      designWidth: DEFAULT_WIDTH,
      designHeight: DEFAULT_HEIGHT,
      showFrame: true,
      camera: { tx: 80, ty: 60, scale: 0.45 },
      activePageId: pageId,
      pages: [
        {
          id: pageId,
          name: '页面 1',
          x: 0,
          y: 0,
          width: DEFAULT_WIDTH,
          height: DEFAULT_HEIGHT,
          elements: [],
        },
      ],
      edges: [],
    };
  }

  function getActivePage() {
    return project.pages.find((p) => p.id === project.activePageId);
  }

  function findPageById(pageId) {
    return project.pages.find((p) => p.id === pageId);
  }

  function findElementOnPage(pageId, nodeId) {
    const page = findPageById(pageId);
    if (!page) return null;
    return page.elements.find((e) => e.id === nodeId) || null;
  }

  /** 端点 nodeId 规范化：undefined/'' 视为「页面」级别 null */
  function normalizeNodeId(nodeId) {
    if (nodeId == null || nodeId === '') return null;
    return nodeId;
  }

  function endpointsEqual(a, b) {
    return a.pageId === b.pageId && normalizeNodeId(a.nodeId) === normalizeNodeId(b.nodeId);
  }

  /**
   * 连线在世界坐标中的端点位置（线段相接）：页面用中心，组件用包围盒中心
   */
  function getEdgeEndpointCenter(pageId, nodeId) {
    const page = findPageById(pageId);
    if (!page) return { cx: 0, cy: 0 };
    const nid = normalizeNodeId(nodeId);
    if (nid == null) {
      return { cx: page.x + page.width / 2, cy: page.y + page.height / 2 };
    }
    const el = findElementOnPage(pageId, nid);
    if (!el) return { cx: page.x + page.width / 2, cy: page.y + page.height / 2 };
    const b = getNodeBoundsWorld(page, el);
    return { cx: b.cx, cy: b.cy };
  }

  /** 从某端点出发的唯一出边终点；若无且仅有一条出边则返回 null */
  function getUniqueOutgoingTarget(pageId, nodeId) {
    const nid = normalizeNodeId(nodeId);
    const outs = project.edges.filter(
      (e) => e.source.pageId === pageId && normalizeNodeId(e.source.nodeId) === nid
    );
    if (outs.length !== 1) return null;
    return outs[0].target;
  }

  function edgeTouchesElementNodeId(edge, nodeId) {
    return (
      (edge.source.nodeId != null && edge.source.nodeId === nodeId) ||
      (edge.target.nodeId != null && edge.target.nodeId === nodeId)
    );
  }

  /** 当前连线起点下，某锚点是否为「已有出边的终点」（点击红色可删该边） */
  function isOutgoingTargetFromConnectAnchor(ep) {
    if (!connectAnchor) return false;
    return project.edges.some(
      (e) => endpointsEqual(e.source, connectAnchor) && endpointsEqual(e.target, ep)
    );
  }

  /**
   * 命中连线锚点（画布坐标 sx,sy）。叠序：后方的页面与上层组件优先。
   * @returns {EdgeEndpoint|null}
   */
  function hitTestConnectAnchor(screenX, screenY) {
    const r = CONNECT_ANCHOR_RADIUS_PX + 2;
    for (let pi = project.pages.length - 1; pi >= 0; pi--) {
      const page = project.pages[pi];
      for (let ei = page.elements.length - 1; ei >= 0; ei--) {
        const el = page.elements[ei];
        const { wx: ax, wy: ay } = getElementConnectAnchorWorld(page, el);
        const sc = worldToScreen(ax, ay);
        if (Math.hypot(screenX - sc.x, screenY - sc.y) <= r) {
          return { pageId: page.id, nodeId: el.id };
        }
      }
      const scp = worldToScreen(page.x, page.y);
      if (Math.hypot(screenX - scp.x, screenY - scp.y) <= r) {
        return { pageId: page.id, nodeId: null };
      }
    }
    return null;
  }

  /**
   * 元素在所属页面内的轴对齐包围盒（局部坐标）
   */
  function getNodeBoundsLocal(el) {
    const sw = el.strokeWidth || DEFAULT_DRAW_STROKE_WIDTH;
    const pad = sw / 2;
    if (el.type === 'rect' || el.type === 'text') {
      const w = el.w || 120;
      const h = el.h || 40;
      return { x: el.x - pad, y: el.y - pad, w: w + sw, h: h + sw, cx: el.x + w / 2, cy: el.y + h / 2 };
    }
    if (el.type === 'ellipse') {
      const w = el.w || 80;
      const h = el.h || 80;
      return { x: el.x - pad, y: el.y - pad, w: w + sw, h: h + sw, cx: el.x + w / 2, cy: el.y + h / 2 };
    }
    if (el.type === 'line') {
      const x1 = el.x;
      const y1 = el.y;
      const x2 = el.x2 ?? el.x;
      const y2 = el.y2 ?? el.y;
      const minX = Math.min(x1, x2) - pad;
      const minY = Math.min(y1, y2) - pad;
      const maxX = Math.max(x1, x2) + pad;
      const maxY = Math.max(y1, y2) + pad;
      return {
        x: minX,
        y: minY,
        w: maxX - minX,
        h: maxY - minY,
        cx: (x1 + x2) / 2,
        cy: (y1 + y2) / 2,
      };
    }
    if (el.type === 'path' && el.points && el.points.length) {
      let minX = Infinity;
      let minY = Infinity;
      let maxX = -Infinity;
      let maxY = -Infinity;
      let any = false;
      for (const pt of el.points) {
        if (pt == null) continue;
        const px = pt[0];
        const py = pt[1];
        minX = Math.min(minX, px);
        minY = Math.min(minY, py);
        maxX = Math.max(maxX, px);
        maxY = Math.max(maxY, py);
        any = true;
      }
      if (!any) return { x: el.x, y: el.y, w: 1, h: 1, cx: el.x, cy: el.y };
      const cx = (minX + maxX) / 2;
      const cy = (minY + maxY) / 2;
      return { x: minX - pad, y: minY - pad, w: maxX - minX + sw, h: maxY - minY + sw, cx, cy };
    }
    return { x: el.x, y: el.y, w: 1, h: 1, cx: el.x, cy: el.y };
  }

  /** 将局部包围盒平移到世界坐标（用于连线端点、居中等） */
  function getNodeBoundsWorld(page, el) {
    const b = getNodeBoundsLocal(el);
    return {
      x: page.x + b.x,
      y: page.y + b.y,
      w: b.w,
      h: b.h,
      cx: page.x + b.cx,
      cy: page.y + b.cy,
    };
  }

  /**
   * 连线锚点（世界坐标）：矩形/椭圆/文本等为组件左上角；手绘 path 与「选中时虚线框」左上角一致。
   */
  function getElementConnectAnchorWorld(page, el) {
    if (el.type === 'path') {
      const bw = getNodeBoundsWorld(page, el);
      return { wx: bw.x, wy: bw.y };
    }
    return { wx: page.x + el.x, wy: page.y + el.y };
  }

  function worldToLocalPage(page, wx, wy) {
    return { x: wx - page.x, y: wy - page.y };
  }

  function isWorldInsidePage(wx, wy, page) {
    return wx >= page.x && wx <= page.x + page.width && wy >= page.y && wy <= page.y + page.height;
  }

  /** 取该点处最上层的页面（pages 数组末尾优先，与绘制叠序一致） */
  function findTopmostPageAtWorld(wx, wy) {
    for (let pi = project.pages.length - 1; pi >= 0; pi--) {
      const pg = project.pages[pi];
      if (isWorldInsidePage(wx, wy, pg)) return pg;
    }
    return null;
  }

  /** 根据节点 id 查找所在页面（id 在项目内唯一） */
  function findPageContainingNode(nodeId) {
    for (const p of project.pages) {
      if (p.elements.some((e) => e.id === nodeId)) return p;
    }
    return null;
  }

  /** 世界坐标下最上层命中节点（用于连线、双击编辑） */
  function hitTestTopMostNodeWorld(wx, wy) {
    for (let pi = project.pages.length - 1; pi >= 0; pi--) {
      const page = project.pages[pi];
      for (let ei = page.elements.length - 1; ei >= 0; ei--) {
        const el = page.elements[ei];
        const b = getNodeBoundsLocal(el);
        const loc = worldToLocalPage(page, wx, wy);
        if (loc.x >= b.x && loc.x <= b.x + b.w && loc.y >= b.y && loc.y <= b.y + b.h) return { page, el };
      }
    }
    return null;
  }

  function resetPickCycle() {
    lastPickScreenX = NaN;
    lastPickScreenY = NaN;
    pickCycleIndex = 0;
  }

  /** 侧栏「当前页面尺寸」与内存数据同步 */
  function syncPageSizeInputs() {
    const page = getActivePage();
    if (!page) return;
    elPageWidth.value = String(page.width);
    elPageHeight.value = String(page.height);
  }

  /**
   * 构建同一点穿透选择顺序：先按绘制顺序列出所有命中节点，再列出命中页面（均由上至下）。
   */
  function buildPickCycleList(wx, wy) {
    const hits = [];
    for (let pi = project.pages.length - 1; pi >= 0; pi--) {
      const page = project.pages[pi];
      for (let ei = page.elements.length - 1; ei >= 0; ei--) {
        const el = page.elements[ei];
        const b = getNodeBoundsLocal(el);
        const loc = worldToLocalPage(page, wx, wy);
        if (loc.x >= b.x && loc.x <= b.x + b.w && loc.y >= b.y && loc.y <= b.y + b.h) {
          hits.push({ kind: 'node', pageId: page.id, nodeId: el.id });
        }
      }
    }
    for (let pi = project.pages.length - 1; pi >= 0; pi--) {
      const page = project.pages[pi];
      if (isWorldInsidePage(wx, wy, page)) hits.push({ kind: 'page', pageId: page.id });
    }
    return hits;
  }

  /**
   * 世界坐标 → 屏幕（画布像素）
   */
  function worldToScreen(wx, wy) {
    return {
      x: wx * camera.scale + camera.tx,
      y: wy * camera.scale + camera.ty,
    };
  }

  /**
   * 屏幕 → 世界坐标（用于点击、拖拽落点）
   */
  function screenToWorld(sx, sy) {
    return {
      x: (sx - camera.tx) / camera.scale,
      y: (sy - camera.ty) / camera.scale,
    };
  }

  // ============================================
  // IndexedDB：打开、读取、写入
  // ============================================

  /**
   * @returns {Promise<IDBDatabase>}
   */
  function openDb() {
    return new Promise((resolve, reject) => {
      const req = indexedDB.open(DB_NAME, 1);
      req.onupgradeneeded = () => {
        const db = req.result;
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          // keyPath: 'key'，存 { key, data }
          db.createObjectStore(STORE_NAME, { keyPath: 'key' });
        }
      };
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error);
    });
  }

  /**
   * 从 IndexedDB 读取项目；没有记录则返回 null
   */
  async function loadProjectFromDb() {
    const db = await openDb();
    return new Promise((resolve, reject) => {
      const tx = db.transaction(STORE_NAME, 'readonly');
      const store = tx.objectStore(STORE_NAME);
      const req = store.get(PROJECT_KEY);
      req.onsuccess = () => resolve(req.result ? req.result.data : null);
      req.onerror = () => reject(req.error);
    });
  }

  /**
   * 将整个 project 对象写入 IndexedDB
   */
  async function saveProjectToDb(data) {
    const db = await openDb();
    return new Promise((resolve, reject) => {
      const tx = db.transaction(STORE_NAME, 'readwrite');
      const store = tx.objectStore(STORE_NAME);
      const req = store.put({ key: PROJECT_KEY, data });
      req.onsuccess = () => resolve();
      req.onerror = () => reject(req.error);
    });
  }

  /**
   * 防抖保存：合并高频变更（拖拽、手绘）
   */
  function scheduleSave() {
    if (saveTimer) clearTimeout(saveTimer);
    elSaveStatus.textContent = '等待保存…';
    elSaveStatus.classList.add('saving');
    elSaveStatus.classList.remove('error');
    saveTimer = setTimeout(async () => {
      saveTimer = null;
      try {
        // 持久化前写入全局相机
        syncCameraToProject();
        await saveProjectToDb(JSON.parse(JSON.stringify(project)));
        elSaveStatus.textContent = '已保存 ' + new Date().toLocaleTimeString();
        elSaveStatus.classList.remove('saving');
      } catch (e) {
        console.error(e);
        elSaveStatus.textContent = '保存失败';
        elSaveStatus.classList.add('error');
        elSaveStatus.classList.remove('saving');
      }
    }, SAVE_DEBOUNCE_MS);
  }

  function syncCameraToProject() {
    project.camera = { ...camera };
    project.activePageId = activePageId;
  }

  function loadCameraFromProject() {
    if (project.camera && typeof project.camera.scale === 'number') {
      camera = { ...project.camera };
    }
  }

  // ============================================
  // 撤销：修改前压栈，Ctrl+Z 恢复上一快照
  // ============================================

  /**
   * 生成当前项目的深拷贝；会先 syncCamera，保证各页的 camera 与当前视图一致。
   */
  function snapshotProjectForUndo() {
    syncCameraToProject();
    return JSON.parse(JSON.stringify(project));
  }

  /**
   * 在执行「可撤销」的修改之前调用：把当前状态压入撤销栈。
   */
  function pushUndo() {
    if (undoRestoring) return;
    undoStack.push(snapshotProjectForUndo());
    while (undoStack.length > MAX_UNDO) undoStack.shift();
  }

  function clearUndoHistory() {
    undoStack = [];
  }

  /**
   * 弹出上一快照并刷新界面；会触发自动保存以同步 IndexedDB。
   */
  function undoLast() {
    if (!undoStack.length || undoRestoring) return;
    undoRestoring = true;
    try {
      const prev = undoStack.pop();
      project = prev;
      activePageId = project.activePageId;
      syncFormFromProject();
      loadCameraFromProject();
      resetPickCycle();
      pageFrameSelectedId = null;
      renderPageList();
      syncPageSizeInputs();
      selectedNodeId = null;
      hideTextEditor();
      connectAnchor = null;
      lineFirstPoint = null;
      dragLocalStart = null;
      drawStrokePageId = '';
      drawPoints = [];
      drawCtrlMergePathId = '';
      drawCtrlMergePageId = '';
      drawStrokeCtrlDown = false;
      moveGrabOffset = null;
      cameraAnim = null;
      projectNameUndoPrimed = true;
      redraw();
      elSaveStatus.textContent = '已撤销';
      scheduleSave();
    } finally {
      undoRestoring = false;
    }
  }

  // ============================================
  // 渲染：网格、分辨率框、元素、连线、选中框
  // ============================================

  function resizeCanvas() {
    const wrap = canvas.parentElement;
    const dpr = window.devicePixelRatio || 1;
    const w = wrap.clientWidth;
    const h = wrap.clientHeight;
    canvas.width = Math.floor(w * dpr);
    canvas.height = Math.floor(h * dpr);
    canvas.style.width = w + 'px';
    canvas.style.height = h + 'px';
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    redraw();
  }

  /**
   * 绘制浅色点阵网格（世界坐标系下随相机移动）
   */
  function drawGrid(cssW, cssH) {
    const step = 80 * camera.scale;
    if (step < 8) return;
    ctx.strokeStyle = 'rgba(255,255,255,0.045)';
    ctx.lineWidth = 1;
    const topLeft = screenToWorld(0, 0);
    const botRight = screenToWorld(cssW, cssH);
    const startX = Math.floor(topLeft.x / 80) * 80;
    const startY = Math.floor(topLeft.y / 80) * 80;
    ctx.beginPath();
    for (let x = startX; x < botRight.x + 80; x += 80) {
      const s = worldToScreen(x, topLeft.y);
      const e = worldToScreen(x, botRight.y);
      ctx.moveTo(s.x, s.y);
      ctx.lineTo(e.x, e.y);
    }
    for (let y = startY; y < botRight.y + 80; y += 80) {
      const s = worldToScreen(topLeft.x, y);
      const e = worldToScreen(botRight.x, y);
      ctx.moveTo(s.x, s.y);
      ctx.lineTo(e.x, e.y);
    }
    ctx.stroke();
  }

  /**
   * 绘制所有页面画板（背景 + 边框）。project.showFrame 为 true 时非当前页面半透明，便于区分画板。
   */
  function drawAllPageFrames() {
    for (let i = 0; i < project.pages.length; i++) {
      const page = project.pages[i];
      const isActive = page.id === project.activePageId;
      const p1 = worldToScreen(page.x, page.y);
      const p2 = worldToScreen(page.x + page.width, page.y + page.height);
      const rw = p2.x - p1.x;
      const rh = p2.y - p1.y;
      ctx.save();
      if (project.showFrame && !isActive) ctx.globalAlpha = 0.38;
      ctx.fillStyle = 'rgba(26,26,31,0.97)';
      ctx.fillRect(p1.x, p1.y, rw, rh);
      ctx.globalAlpha = 1;
      ctx.strokeStyle = isActive ? '#a8bfd9' : 'rgba(255,255,255,0.14)';
      ctx.lineWidth = isActive ? 1.5 : 1;
      ctx.setLineDash([]);
      ctx.strokeRect(p1.x, p1.y, rw, rh);
      ctx.fillStyle = 'rgba(152,152,166,0.92)';
      ctx.font = `${Math.max(10, 12 * camera.scale)}px "Segoe UI","PingFang SC",sans-serif`;
      ctx.fillText(page.name, p1.x + 8 * camera.scale, p1.y + 16 * camera.scale);
      ctx.restore();
    }
  }

  /**
   * el 的 x,y 等为页面局部坐标，此处叠加 page 原点变换到世界再投影到屏幕
   */
  function drawElement(page, el, isSelected) {
    const ox = page.x + el.x;
    const oy = page.y + el.y;
    const isText = el.type === 'text';
    const stroke =
      el.stroke != null && el.stroke !== '' ? el.stroke : isText ? '#ececf1' : DEFAULT_DRAW_STROKE;
    let fill;
    if (el.fill != null && el.fill !== '') {
      fill = el.fill;
    } else if (el.type === 'rect' || el.type === 'ellipse') {
      fill = 'transparent';
    } else if (isText) {
      fill = 'rgba(36,36,42,0.94)';
    } else {
      fill = 'rgba(255,255,255,0.055)';
    }
    const lw = el.strokeWidth != null && el.strokeWidth !== '' ? el.strokeWidth : DEFAULT_DRAW_STROKE_WIDTH;
    ctx.lineWidth = Math.max(1, lw * camera.scale);
    ctx.strokeStyle = stroke;
    ctx.fillStyle = fill;

    if (el.type === 'rect') {
      const p = worldToScreen(ox, oy);
      const sw = (el.w || 120) * camera.scale;
      const sh = (el.h || 80) * camera.scale;
      ctx.fillRect(p.x, p.y, sw, sh);
      ctx.strokeRect(p.x, p.y, sw, sh);
    } else if (el.type === 'ellipse') {
      const p = worldToScreen(ox, oy);
      const sw = (el.w || 80) * camera.scale;
      const sh = (el.h || 80) * camera.scale;
      const cx = p.x + sw / 2;
      const cy = p.y + sh / 2;
      ctx.beginPath();
      ctx.ellipse(cx, cy, Math.abs(sw / 2), Math.abs(sh / 2), 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
    } else if (el.type === 'line') {
      const p1 = worldToScreen(page.x + el.x, page.y + el.y);
      const p2 = worldToScreen(page.x + (el.x2 ?? el.x), page.y + (el.y2 ?? el.y));
      ctx.beginPath();
      ctx.moveTo(p1.x, p1.y);
      ctx.lineTo(p2.x, p2.y);
      ctx.stroke();
    } else if (el.type === 'path' && el.points && el.points.length > 1) {
      ctx.beginPath();
      let penDown = false;
      for (let i = 0; i < el.points.length; i++) {
        const raw = el.points[i];
        if (raw == null) {
          penDown = false;
          continue;
        }
        const scr = worldToScreen(page.x + raw[0], page.y + raw[1]);
        if (!penDown) {
          ctx.moveTo(scr.x, scr.y);
          penDown = true;
        } else {
          ctx.lineTo(scr.x, scr.y);
        }
      }
      ctx.stroke();
    } else if (el.type === 'text') {
      const p = worldToScreen(ox, oy);
      const fs = (el.fontSize || 16) * camera.scale;
      ctx.font = `${fs}px "Segoe UI","PingFang SC","Microsoft YaHei",sans-serif`;
      ctx.textBaseline = 'top';
      const lines = (el.text || '文本').split('\n');
      let ly = p.y;
      const lineHeight = fs * 1.25;
      const maxW = (el.w || 200) * camera.scale;
      ctx.fillStyle = fill;
      ctx.fillRect(p.x - 2, p.y - 2, maxW + 4, lines.length * lineHeight + 4);
      ctx.fillStyle = stroke;
      for (const line of lines) {
        ctx.fillText(line, p.x, ly, maxW);
        ly += lineHeight;
      }
      ctx.strokeStyle = stroke;
      ctx.strokeRect(p.x - 2, p.y - 2, maxW + 4, lines.length * lineHeight + 4);
    }

    if (isSelected) {
      const b = getNodeBoundsWorld(page, el);
      const p = worldToScreen(b.x, b.y);
      ctx.save();
      ctx.strokeStyle = '#a8bfd9';
      ctx.lineWidth = 1.5;
      ctx.setLineDash([6, 4]);
      ctx.strokeRect(p.x, p.y, b.w * camera.scale, b.h * camera.scale);
      ctx.restore();
    }
  }

  /** 全部连线（跨画板），端点取世界坐标下元素包围盒中心 */
  function drawAllEdges() {
    ctx.strokeStyle = 'rgba(255,255,255,0.2)';
    ctx.lineWidth = Math.max(1, 1.5 * camera.scale);
    ctx.setLineDash([6, 6]);

    for (const edge of project.edges) {
      const pa = findPageById(edge.source.pageId);
      const pb = findPageById(edge.target.pageId);
      if (!pa || !pb) continue;
      const ca = getEdgeEndpointCenter(edge.source.pageId, edge.source.nodeId);
      const cb = getEdgeEndpointCenter(edge.target.pageId, edge.target.nodeId);
      const pta = worldToScreen(ca.cx, ca.cy);
      const ptb = worldToScreen(cb.cx, cb.cy);
      ctx.beginPath();
      ctx.moveTo(pta.x, pta.y);
      ctx.lineTo(ptb.x, ptb.y);
      ctx.stroke();

      const ang = Math.atan2(ptb.y - pta.y, ptb.x - pta.x);
      const sz = 10 + camera.scale * 4;
      ctx.setLineDash([]);
      ctx.fillStyle = 'rgba(190,190,200,0.5)';
      ctx.beginPath();
      ctx.moveTo(ptb.x, ptb.y);
      ctx.lineTo(ptb.x - sz * Math.cos(ang - 0.45), ptb.y - sz * Math.sin(ang - 0.45));
      ctx.lineTo(ptb.x - sz * Math.cos(ang + 0.45), ptb.y - sz * Math.sin(ang + 0.45));
      ctx.closePath();
      ctx.fill();
      ctx.setLineDash([6, 6]);
    }
    ctx.setLineDash([]);
  }

  function redraw() {
    const cssW = canvas.clientWidth;
    const cssH = canvas.clientHeight;
    ctx.clearRect(0, 0, cssW, cssH);

    drawGrid(cssW, cssH);
    drawAllPageFrames();

    for (const pg of project.pages) {
      for (const el of pg.elements) {
        drawElement(pg, el, el.id === selectedNodeId);
      }
    }

    drawAllEdges();
    drawConnectAnchors();
    tickCameraAnim();
  }

  /** 连线工具：手绘路径显示包围盒虚线；再绘制绿/红锚点（线段仍连几何中心） */
  function drawConnectAnchors() {
    if (currentTool !== 'connect') return;

    ctx.save();
    ctx.strokeStyle = 'rgba(168, 191, 217, 0.32)';
    ctx.lineWidth = 1;
    ctx.setLineDash([6, 4]);
    for (const page of project.pages) {
      for (const el of page.elements) {
        if (el.type !== 'path') continue;
        const bw = getNodeBoundsWorld(page, el);
        const p = worldToScreen(bw.x, bw.y);
        ctx.strokeRect(p.x, p.y, bw.w * camera.scale, bw.h * camera.scale);
      }
    }
    ctx.restore();

    const r = CONNECT_ANCHOR_RADIUS_PX;

    function paint(wx, wy, ep) {
      const sc = worldToScreen(wx, wy);
      const isSelStart = connectAnchor && endpointsEqual(ep, connectAnchor);
      const isRed = connectAnchor && isOutgoingTargetFromConnectAnchor(ep) && !isSelStart;
      ctx.beginPath();
      ctx.arc(sc.x, sc.y, r, 0, Math.PI * 2);
      if (isRed) {
        ctx.fillStyle = '#9f2d3a';
        ctx.strokeStyle = 'rgba(252, 165, 165, 0.75)';
      } else {
        ctx.fillStyle = '#5c5c66';
        ctx.strokeStyle = '#d4d4d8';
      }
      ctx.lineWidth = 1.25;
      ctx.fill();
      ctx.stroke();
      if (isSelStart) {
        ctx.beginPath();
        ctx.arc(sc.x, sc.y, r + 4, 0, Math.PI * 2);
        ctx.strokeStyle = '#ececf1';
        ctx.lineWidth = 1.5;
        ctx.stroke();
      }
    }

    for (let pi = 0; pi < project.pages.length; pi++) {
      const page = project.pages[pi];
      for (const el of page.elements) {
        const { wx, wy } = getElementConnectAnchorWorld(page, el);
        paint(wx, wy, { pageId: page.id, nodeId: el.id });
      }
      paint(page.x, page.y, { pageId: page.id, nodeId: null });
    }
  }

  /**
   * 相机动画：平滑移动到目标（居中节点时使用）
   */
  function tickCameraAnim() {
    if (!cameraAnim) return;
    const now = performance.now();
    const t = Math.min(1, (now - cameraAnim.startTime) / cameraAnim.duration);
    const ease = 1 - Math.pow(1 - t, 3);
    camera.tx = cameraAnim.from.tx + (cameraAnim.to.tx - cameraAnim.from.tx) * ease;
    camera.ty = cameraAnim.from.ty + (cameraAnim.to.ty - cameraAnim.from.ty) * ease;
    camera.scale = cameraAnim.from.scale + (cameraAnim.to.scale - cameraAnim.from.scale) * ease;
    if (t >= 1) cameraAnim = null;
    else requestAnimationFrame(redraw);
  }

  function animateCameraTo(toTx, toTy, toScale, duration = 420) {
    cameraAnim = {
      startTime: performance.now(),
      duration,
      from: { ...camera },
      to: { tx: toTx, ty: toTy, scale: toScale },
    };
    requestAnimationFrame(redraw);
  }

  /**
   * 将世界坐标点 (cx,cy) 对齐到画布中心，保持当前 scale
   */
  function centerWorldPoint(cx, cy) {
    const cssW = canvas.clientWidth;
    const cssH = canvas.clientHeight;
    const toTx = cssW / 2 - cx * camera.scale;
    const toTy = cssH / 2 - cy * camera.scale;
    animateCameraTo(toTx, toTy, camera.scale);
  }

  /**
   * 双击沿「唯一出边」跳转：仅当该端点恰好有一条出边时生效。
   * @returns {boolean} 是否已执行跳转
   */
  function navigateAlongUniqueOutgoing(pageId, nodeId) {
    const tgt = getUniqueOutgoingTarget(pageId, nodeId);
    if (!tgt) return false;
    resetPickCycle();
    const c = getEdgeEndpointCenter(tgt.pageId, tgt.nodeId);
    centerWorldPoint(c.cx, c.cy);
    const nid = normalizeNodeId(tgt.nodeId);
    project.activePageId = tgt.pageId;
    activePageId = tgt.pageId;
    if (nid != null) {
      selectedNodeId = nid;
      pageFrameSelectedId = null;
    } else {
      selectedNodeId = null;
      pageFrameSelectedId = tgt.pageId;
    }
    renderPageList();
    syncPageSizeInputs();
    scheduleSave();
    redraw();
    return true;
  }

  // ============================================
  // 图结构：邻接（支持页面级端点 nodeId === null）
  // ============================================

  /**
   * 收集与某节点关联的所有边（无向意义上的邻接）
   */
  /**
   * 选择工具点击：同屏幕位置连击时在穿透列表中轮换；最后一档为选中页面画板。
   * 沿连线跳转改为双击（见 dblclick），避免与穿透选择冲突。
   * @returns {{ jumped: boolean, startDrag: { pageId: string, nodeId: string } | null }}
   */
  function handleSelectClick(worldX, worldY, screenSX, screenSY) {
    const list = buildPickCycleList(worldX, worldY);
    if (!list.length) {
      resetPickCycle();
      pageFrameSelectedId = null;
      selectedNodeId = null;
      hideTextEditor();
      redraw();
      return { jumped: false, startDrag: null };
    }

    const sameSpot =
      Number.isFinite(lastPickScreenX) &&
      Math.hypot(screenSX - lastPickScreenX, screenSY - lastPickScreenY) < PICK_CYCLE_RADIUS_PX;
    if (!sameSpot) pickCycleIndex = 0;
    else pickCycleIndex = (pickCycleIndex + 1) % list.length;

    lastPickScreenX = screenSX;
    lastPickScreenY = screenSY;

    const pick = list[pickCycleIndex];

    if (pick.kind === 'page') {
      project.activePageId = pick.pageId;
      activePageId = pick.pageId;
      pageFrameSelectedId = pick.pageId;
      selectedNodeId = null;
      hideTextEditor();
      renderPageList();
      syncPageSizeInputs();
      redraw();
      return { jumped: false, startDrag: null };
    }

    pageFrameSelectedId = null;
    project.activePageId = pick.pageId;
    activePageId = pick.pageId;
    renderPageList();
    syncPageSizeInputs();

    selectedNodeId = pick.nodeId;
    redraw();
    return { jumped: false, startDrag: { pageId: pick.pageId, nodeId: pick.nodeId } };
  }

  // ============================================
  // 交互：指针、滚轮、键盘
  // ============================================

  function updateCanvasCursor() {
    canvas.classList.remove('cursor-grab', 'cursor-grabbing');
    if (moveGrabOffset && moveGrabOffset.kind === 'move-page') {
      canvas.classList.add('cursor-grabbing');
      return;
    }
    if (spaceDown) {
      canvas.classList.add(moveGrabOffset ? 'cursor-grabbing' : 'cursor-grab');
    }
  }

  canvas.addEventListener('wheel', (ev) => {
    ev.preventDefault();
    const wrap = canvas.getBoundingClientRect();
    const sx = ev.clientX - wrap.left;
    const sy = ev.clientY - wrap.top;
    const before = screenToWorld(sx, sy);
    const delta = ev.deltaY > 0 ? 0.92 : 1.09;
    const nextScale = Math.min(4, Math.max(0.08, camera.scale * delta));
    camera.scale = nextScale;
    // 缩放锚定在鼠标下：保持 before 点仍在鼠标下
    camera.tx = sx - before.x * camera.scale;
    camera.ty = sy - before.y * camera.scale;
    redraw();
    scheduleSave();
  }, { passive: false });

  canvas.addEventListener('pointerdown', (ev) => {
    canvas.focus();
    const wrap = canvas.getBoundingClientRect();
    const sx = ev.clientX - wrap.left;
    const sy = ev.clientY - wrap.top;
    const w = screenToWorld(sx, sy);

    if (spaceDown || ev.button === 1) {
      canvas.setPointerCapture(ev.pointerId);
      moveGrabOffset = { sx, sy, ctxTx: camera.tx, ctxTy: camera.ty };
      updateCanvasCursor();
      return;
    }

    if (currentTool === 'select') {
      let pgMove = null;
      if (ev.altKey) {
        pgMove = findTopmostPageAtWorld(w.x, w.y);
      } else if (pageFrameSelectedId) {
        const pf = findPageById(pageFrameSelectedId);
        if (pf && !hitTestTopMostNodeWorld(w.x, w.y) && isWorldInsidePage(w.x, w.y, pf)) {
          pgMove = pf;
        }
      }
      if (pgMove) {
        pushUndo();
        canvas.setPointerCapture(ev.pointerId);
        moveGrabOffset = {
          kind: 'move-page',
          pageId: pgMove.id,
          grabWx: w.x,
          grabWy: w.y,
          startX: pgMove.x,
          startY: pgMove.y,
        };
        updateCanvasCursor();
        return;
      }

      const sel = handleSelectClick(w.x, w.y, sx, sy);
      if (sel.jumped) return;
      if (sel.startDrag) {
        pushUndo();
        canvas.setPointerCapture(ev.pointerId);
        const p = findPageById(sel.startDrag.pageId);
        const hit = p.elements.find((e) => e.id === sel.startDrag.nodeId);
        if (!hit) return;
        const loc = worldToLocalPage(p, w.x, w.y);
        moveGrabOffset = {
          kind: 'move-node',
          pageId: sel.startDrag.pageId,
          nodeId: sel.startDrag.nodeId,
          offsetX: loc.x - hit.x,
          offsetY: loc.y - hit.y,
          grabWx: w.x,
          grabWy: w.y,
        };
      }
      return;
    }

    if (currentTool === 'connect') {
      const hitEp = hitTestConnectAnchor(sx, sy);
      if (!hitEp) return;

      if (!connectAnchor) {
        connectAnchor = { pageId: hitEp.pageId, nodeId: normalizeNodeId(hitEp.nodeId) };
        redraw();
        return;
      }

      if (endpointsEqual(connectAnchor, hitEp)) {
        connectAnchor = null;
        redraw();
        return;
      }

      const existingOut = project.edges.find(
        (e) => endpointsEqual(e.source, connectAnchor) && endpointsEqual(e.target, hitEp)
      );
      if (existingOut) {
        pushUndo();
        project.edges = project.edges.filter((e) => e.id !== existingOut.id);
        connectAnchor = null;
        scheduleSave();
        redraw();
        return;
      }

      pushUndo();
      project.edges.push({
        id: newId(),
        source: { pageId: connectAnchor.pageId, nodeId: normalizeNodeId(connectAnchor.nodeId) },
        target: { pageId: hitEp.pageId, nodeId: normalizeNodeId(hitEp.nodeId) },
      });
      connectAnchor = null;
      scheduleSave();
      redraw();
      return;
    }

    const page = getActivePage();
    if (!page) return;

    if (currentTool === 'line') {
      if (!isWorldInsidePage(w.x, w.y, page)) {
        if (lineFirstPoint) lineFirstPoint = null;
        return;
      }
      const loc = worldToLocalPage(page, w.x, w.y);
      if (!lineFirstPoint) {
        lineFirstPoint = { pageId: page.id, x: loc.x, y: loc.y };
      } else {
        if (lineFirstPoint.pageId !== page.id) {
          lineFirstPoint = { pageId: page.id, x: loc.x, y: loc.y };
          return;
        }
        pushUndo();
        page.elements.push({
          id: newId(),
          type: 'line',
          x: lineFirstPoint.x,
          y: lineFirstPoint.y,
          x2: loc.x,
          y2: loc.y,
          stroke: DEFAULT_DRAW_STROKE,
          strokeWidth: DEFAULT_DRAW_STROKE_WIDTH,
        });
        lineFirstPoint = null;
        scheduleSave();
        redraw();
      }
      return;
    }

    if (!isWorldInsidePage(w.x, w.y, page)) return;

    if (currentTool === 'rect' || currentTool === 'ellipse') {
      const loc = worldToLocalPage(page, w.x, w.y);
      dragLocalStart = { x: loc.x, y: loc.y, tool: currentTool, pageId: page.id };
      canvas.setPointerCapture(ev.pointerId);
      return;
    }

    if (currentTool === 'draw') {
      const loc = worldToLocalPage(page, w.x, w.y);
      drawStrokePageId = page.id;
      drawPoints = [[loc.x, loc.y]];
      drawStrokeCtrlDown = !!(ev.ctrlKey || ev.metaKey);
      if (drawStrokeCtrlDown && drawCtrlMergePathId && drawCtrlMergePageId === page.id) {
        const exist = page.elements.find((e) => e.id === drawCtrlMergePathId && e.type === 'path');
        if (!exist) {
          drawCtrlMergePathId = '';
          drawCtrlMergePageId = '';
        }
      }
      if (!drawStrokeCtrlDown) {
        drawCtrlMergePathId = '';
        drawCtrlMergePageId = '';
      }
      canvas.setPointerCapture(ev.pointerId);
      return;
    }

    if (currentTool === 'text') {
      pushUndo();
      const loc = worldToLocalPage(page, w.x, w.y);
      page.elements.push({
        id: newId(),
        type: 'text',
        x: loc.x,
        y: loc.y,
        w: 220,
        h: 72,
        text: '双击编辑文本',
        fill: 'rgba(36,36,42,0.94)',
        stroke: '#71717a',
        strokeWidth: 1,
        fontSize: 16,
      });
      scheduleSave();
      redraw();
    }
  });

  canvas.addEventListener('pointermove', (ev) => {
    const wrap = canvas.getBoundingClientRect();
    const sx = ev.clientX - wrap.left;
    const sy = ev.clientY - wrap.top;

    if (moveGrabOffset && moveGrabOffset.ctxTx !== undefined) {
      camera.tx = moveGrabOffset.ctxTx + (sx - moveGrabOffset.sx);
      camera.ty = moveGrabOffset.ctxTy + (sy - moveGrabOffset.sy);
      redraw();
      return;
    }

    if (moveGrabOffset && moveGrabOffset.kind === 'move-page') {
      const pg = findPageById(moveGrabOffset.pageId);
      if (pg) {
        const wpt = screenToWorld(sx, sy);
        pg.x = moveGrabOffset.startX + (wpt.x - moveGrabOffset.grabWx);
        pg.y = moveGrabOffset.startY + (wpt.y - moveGrabOffset.grabWy);
      }
      redraw();
      return;
    }

    if (moveGrabOffset && moveGrabOffset.kind === 'move-node') {
      const page = findPageById(moveGrabOffset.pageId);
      if (!page) return;
      const el = page.elements.find((e) => e.id === moveGrabOffset.nodeId);
      if (el) {
        const w = screenToWorld(sx, sy);
        if (el.type === 'line') {
          const dx = w.x - moveGrabOffset.grabWx;
          const dy = w.y - moveGrabOffset.grabWy;
          el.x += dx;
          el.y += dy;
          el.x2 = (el.x2 ?? el.x) + dx;
          el.y2 = (el.y2 ?? el.y) + dy;
          moveGrabOffset.grabWx = w.x;
          moveGrabOffset.grabWy = w.y;
        } else if (el.type === 'path' && el.points) {
          const dx = w.x - moveGrabOffset.grabWx;
          const dy = w.y - moveGrabOffset.grabWy;
          el.points = el.points.map((pt) => (pt == null ? null : [pt[0] + dx, pt[1] + dy]));
          moveGrabOffset.grabWx = w.x;
          moveGrabOffset.grabWy = w.y;
        } else {
          const loc = worldToLocalPage(page, w.x, w.y);
          el.x = loc.x - moveGrabOffset.offsetX;
          el.y = loc.y - moveGrabOffset.offsetY;
        }
      }
      redraw();
      return;
    }

    if (dragLocalStart && (dragLocalStart.tool === 'rect' || dragLocalStart.tool === 'ellipse')) {
      const page = findPageById(dragLocalStart.pageId);
      if (!page) return;
      redraw();
      const w = screenToWorld(sx, sy);
      const loc2 = worldToLocalPage(page, w.x, w.y);
      previewRectEllipseLocal(page, dragLocalStart, loc2);
      return;
    }

    if (drawPoints.length && drawStrokePageId) {
      const page = findPageById(drawStrokePageId);
      if (!page) return;
      const w = screenToWorld(sx, sy);
      const loc = worldToLocalPage(page, w.x, w.y);
      const last = drawPoints[drawPoints.length - 1];
      const dist = Math.hypot(loc.x - last[0], loc.y - last[1]);
      if (dist > 2 / camera.scale) drawPoints.push([loc.x, loc.y]);
      redraw();
      previewPath(page);
    }
  });

  canvas.addEventListener('pointerup', (ev) => {
    if (moveGrabOffset && moveGrabOffset.ctxTx !== undefined) {
      moveGrabOffset = null;
      scheduleSave();
      updateCanvasCursor();
      redraw();
      return;
    }

    if (moveGrabOffset && moveGrabOffset.kind === 'move-node') {
      moveGrabOffset = null;
      scheduleSave();
      redraw();
      return;
    }

    if (moveGrabOffset && moveGrabOffset.kind === 'move-page') {
      moveGrabOffset = null;
      scheduleSave();
      updateCanvasCursor();
      redraw();
      return;
    }

    if (dragLocalStart) {
      const wrap = canvas.getBoundingClientRect();
      const sx = ev.clientX - wrap.left;
      const sy = ev.clientY - wrap.top;
      const w2 = screenToWorld(sx, sy);
      const page = findPageById(dragLocalStart.pageId);
      if (page) {
        const loc2 = worldToLocalPage(page, w2.x, w2.y);
        const x = Math.min(dragLocalStart.x, loc2.x);
        const y = Math.min(dragLocalStart.y, loc2.y);
        const rw = Math.abs(loc2.x - dragLocalStart.x);
        const rh = Math.abs(loc2.y - dragLocalStart.y);
        if (rw > 4 && rh > 4) {
          pushUndo();
          page.elements.push({
            id: newId(),
            type: dragLocalStart.tool === 'rect' ? 'rect' : 'ellipse',
            x,
            y,
            w: rw,
            h: rh,
            fill: 'transparent',
            stroke: DEFAULT_DRAW_STROKE,
            strokeWidth: DEFAULT_DRAW_STROKE_WIDTH,
          });
          scheduleSave();
        }
      }
      dragLocalStart = null;
      redraw();
      return;
    }

    if (drawPoints.length && drawStrokePageId) {
      const page = findPageById(drawStrokePageId);
      if (page && drawPoints.length > 2) {
        const wantMerge =
          drawStrokeCtrlDown &&
          drawCtrlMergePathId &&
          drawCtrlMergePageId === page.id;
        let merged = false;
        if (wantMerge) {
          const el = page.elements.find((e) => e.id === drawCtrlMergePathId && e.type === 'path');
          if (el && el.points && el.points.length) {
            pushUndo();
            el.points = el.points.concat([null], drawPoints.slice());
            const firstPt = el.points.find((p) => p != null);
            if (firstPt) {
              el.x = firstPt[0];
              el.y = firstPt[1];
            }
            scheduleSave();
            merged = true;
          }
        }
        if (!merged) {
          pushUndo();
          const nid = newId();
          page.elements.push({
            id: nid,
            type: 'path',
            x: drawPoints[0][0],
            y: drawPoints[0][1],
            points: drawPoints.slice(),
            stroke: DEFAULT_DRAW_STROKE,
            strokeWidth: DEFAULT_DRAW_STROKE_WIDTH,
          });
          if (drawStrokeCtrlDown) {
            drawCtrlMergePathId = nid;
            drawCtrlMergePageId = page.id;
          } else {
            drawCtrlMergePathId = '';
            drawCtrlMergePageId = '';
          }
          scheduleSave();
        }
      }
      drawPoints = [];
      drawStrokePageId = '';
      drawStrokeCtrlDown = false;
      redraw();
    }

    try {
      canvas.releasePointerCapture(ev.pointerId);
    } catch (_) {}
  });

  canvas.addEventListener('pointercancel', () => {
    moveGrabOffset = null;
    dragLocalStart = null;
    drawStrokePageId = '';
    drawPoints = [];
    drawStrokeCtrlDown = false;
    drawCtrlMergePathId = '';
    drawCtrlMergePageId = '';
    redraw();
  });

  /** 拖拽创建矩形/椭圆：局部坐标预览 */
  function previewRectEllipseLocal(page, startLoc, endLoc) {
    const x = Math.min(startLoc.x, endLoc.x);
    const y = Math.min(startLoc.y, endLoc.y);
    const rw = Math.abs(endLoc.x - startLoc.x);
    const rh = Math.abs(endLoc.y - startLoc.y);
    const p = worldToScreen(page.x + x, page.y + y);
    ctx.save();
    ctx.strokeStyle = 'rgba(200,200,210,0.45)';
    ctx.lineWidth = Math.max(1, DEFAULT_DRAW_STROKE_WIDTH * camera.scale);
    ctx.setLineDash([8, 4]);
    ctx.strokeRect(p.x, p.y, rw * camera.scale, rh * camera.scale);
    ctx.restore();
  }

  function previewPath(page) {
    if (drawPoints.length < 2 || !page) return;
    ctx.save();
    ctx.strokeStyle = 'rgba(200,200,210,0.45)';
    ctx.lineWidth = Math.max(1, DEFAULT_DRAW_STROKE_WIDTH * camera.scale);
    ctx.beginPath();
    const f = worldToScreen(page.x + drawPoints[0][0], page.y + drawPoints[0][1]);
    ctx.moveTo(f.x, f.y);
    for (let i = 1; i < drawPoints.length; i++) {
      const pt = worldToScreen(page.x + drawPoints[i][0], page.y + drawPoints[i][1]);
      ctx.lineTo(pt.x, pt.y);
    }
    ctx.stroke();
    ctx.restore();
  }

  /** 焦点在可编辑控件内时不应触发画布快捷键 */
  function isFormFieldFocused() {
    const ae = document.activeElement;
    return ae && (ae.tagName === 'INPUT' || ae.tagName === 'TEXTAREA');
  }

  window.addEventListener('keydown', (ev) => {
    // Ctrl+Z / Cmd+Z：撤销（在输入框/文本域内不拦截，保留系统默认的文本撤销）
    if ((ev.ctrlKey || ev.metaKey) && ev.code === 'KeyZ' && !ev.shiftKey) {
      if (isFormFieldFocused()) return;
      ev.preventDefault();
      undoLast();
      return;
    }

    if (ev.code === 'Space') {
      if (isFormFieldFocused()) return;
      // 防止空格滚动页面
      if (document.activeElement === canvas || canvas.contains(document.activeElement)) ev.preventDefault();
      spaceDown = true;
      updateCanvasCursor();
    }

    const letterTools = {
      KeyV: 'select',
      KeyR: 'rect',
      KeyE: 'ellipse',
      KeyL: 'line',
      KeyB: 'draw',
      KeyT: 'text',
      KeyC: 'connect',
    };
    const digitTools = {
      Digit1: 'select',
      Digit2: 'rect',
      Digit3: 'ellipse',
      Digit4: 'line',
      Digit5: 'draw',
      Digit6: 'text',
      Digit7: 'connect',
    };

    if (
      !ev.ctrlKey &&
      !ev.metaKey &&
      !ev.altKey &&
      !isFormFieldFocused()
    ) {
      const lt = letterTools[ev.code];
      if (lt) {
        ev.preventDefault();
        setTool(lt);
      }
      const dt = digitTools[ev.code];
      if (dt) {
        ev.preventDefault();
        setTool(dt);
      }
    }

    if (ev.key === 'Delete' || ev.key === 'Backspace') {
      if (document.activeElement === textEditor) return;
      if (isFormFieldFocused()) return;
      deleteSelected();
    }
  });

  window.addEventListener('keyup', (ev) => {
    if (ev.code === 'Space') {
      spaceDown = false;
      updateCanvasCursor();
    }
  });

  canvas.addEventListener('dblclick', (ev) => {
    if (currentTool !== 'select') return;
    const wrap = canvas.getBoundingClientRect();
    const sx = ev.clientX - wrap.left;
    const sy = ev.clientY - wrap.top;
    const w = screenToWorld(sx, sy);
    const hitObj = hitTestTopMostNodeWorld(w.x, w.y);
    if (hitObj && hitObj.el.type === 'text') {
      openTextEditor(hitObj.page, hitObj.el);
      ev.preventDefault();
      return;
    }
    if (hitObj) {
      if (navigateAlongUniqueOutgoing(hitObj.page.id, hitObj.el.id)) ev.preventDefault();
      return;
    }
    const pg = findTopmostPageAtWorld(w.x, w.y);
    if (pg && isWorldInsidePage(w.x, w.y, pg)) {
      if (navigateAlongUniqueOutgoing(pg.id, null)) ev.preventDefault();
    }
  });

  function openTextEditor(page, el) {
    const p = worldToScreen(page.x + el.x, page.y + el.y);
    const sw = (el.w || 200) * camera.scale;
    const sh = Math.max(40, (el.h || 72) * camera.scale);
    textEditor.value = el.text || '';
    textEditor.hidden = false;
    textEditor.style.left = canvas.getBoundingClientRect().left + p.x + 'px';
    textEditor.style.top = canvas.getBoundingClientRect().top + p.y + 'px';
    textEditor.style.width = sw + 'px';
    textEditor.style.height = sh + 'px';
    textEditor.dataset.nodeId = el.id;
    textEditor.focus();
  }

  function hideTextEditor() {
    textEditor.hidden = true;
    textEditor.dataset.nodeId = '';
  }

  textEditor.addEventListener('blur', () => {
    const id = textEditor.dataset.nodeId;
    if (!id) return;
    const page = findPageContainingNode(id);
    if (!page) return;
    const el = page.elements.find((e) => e.id === id);
    if (el && el.type === 'text') {
      const next = textEditor.value || ' ';
      if (next !== el.text) pushUndo();
      el.text = next;
      scheduleSave();
      redraw();
    }
    hideTextEditor();
  });

  function deleteSelected() {
    if (!selectedNodeId) return;
    const page = findPageContainingNode(selectedNodeId);
    if (!page) return;
    pushUndo();
    const id = selectedNodeId;
    page.elements = page.elements.filter((e) => e.id !== id);
    // 节点 id 在整个项目中唯一；页面级端点（nodeId 为 null）不受影响
    project.edges = project.edges.filter((e) => !edgeTouchesElementNodeId(e, id));
    if (drawCtrlMergePathId === id) {
      drawCtrlMergePathId = '';
      drawCtrlMergePageId = '';
    }
    selectedNodeId = null;
    scheduleSave();
    redraw();
  }

  elBtnDelete.addEventListener('click', deleteSelected);

  /**
   * 两页面画板外框是否「冲突」：重叠或间距小于 gap（与新建页间距 PAGE_GAP 一致）
   */
  function pageBoardsConflict(ax, ay, aw, ah, bx, by, bw, bh, gap) {
    return !(ax + aw + gap <= bx || bx + bw + gap <= ax || ay + ah + gap <= by || by + bh + gap <= ay);
  }

  function pageConflictsAnyPlaced(x, y, w, h, placed, gap) {
    for (let i = 0; i < placed.length; i++) {
      const r = placed[i];
      if (pageBoardsConflict(x, y, w, h, r.x, r.y, r.w, r.h, gap)) return true;
    }
    return false;
  }

  /**
   * 在网格上以 (gx,gy) 为首选左上角，按 Chebyshev 距离向外找第一个不与 placed 冲突的位置
   */
  function findGridSlotForPage(page, gx, gy, cellW, cellH, placed, gap) {
    const w = page.width;
    const h = page.height;
    const maxShell = 2000;
    for (let shell = 0; shell < maxShell; shell++) {
      for (let u = -shell; u <= shell; u++) {
        for (let v = -shell; v <= shell; v++) {
          if (Math.max(Math.abs(u), Math.abs(v)) !== shell) continue;
          const cx = gx + u * cellW;
          const cy = gy + v * cellH;
          if (!pageConflictsAnyPlaced(cx, cy, w, h, placed, gap)) return { x: cx, y: cy };
        }
      }
    }
    return { x: gx, y: gy };
  }

  /**
   * 将所有页面左上角对齐到步长为 (designWidth+200) × (designHeight+200) 的网格；
   * 按 pages 数组顺序消解重叠（后者沿网格外扩）。
   */
  function alignAllPagesToGrid() {
    if (!project.pages.length) return;
    const cellW = project.designWidth + GRID_ALIGN_EXTRA;
    const cellH = project.designHeight + GRID_ALIGN_EXTRA;
    const gap = PAGE_GAP;
    pushUndo();
    const placed = [];
    for (let i = 0; i < project.pages.length; i++) {
      const p = project.pages[i];
      const gx = Math.round(p.x / cellW) * cellW;
      const gy = Math.round(p.y / cellH) * cellH;
      const pos = findGridSlotForPage(p, gx, gy, cellW, cellH, placed, gap);
      p.x = pos.x;
      p.y = pos.y;
      placed.push({ x: p.x, y: p.y, w: p.width, h: p.height });
    }
    scheduleSave();
    redraw();
  }

  if (elBtnAlignGrid) elBtnAlignGrid.addEventListener('click', alignAllPagesToGrid);

  // ============================================
  // UI：工具栏、页面列表、表单
  // ============================================

  /** 画布底部提示：仅在连线工具下显示锚点说明，其它工具显示通用说明 */
  function updateCanvasHint() {
    if (!elCanvasHint) return;
    const suffix = ' · Alt 拖页面 · 空格平移 · Ctrl+Z';
    const general = '工具 V/R/E/L/B/T/C 或 1–7 · 双击组件/页面：唯一出边则跳转终点' + suffix;
    const drawHint =
      '手绘工具：落笔绘制路径；笔触按下时按住 Ctrl（Mac：⌘），松笔后多段笔划会并入同一路径组件；未按 Ctrl 则每次松笔新建路径' + suffix;
    const connectHint =
      '连线工具：手绘显示蓝色虚线包围盒；绿色锚点接起点与终点（手绘锚点在包围盒左上角）；已定起点后红色为已有终点，点此删线；再点同一绿色起点取消' +
      suffix;
    if (currentTool === 'connect') elCanvasHint.textContent = connectHint;
    else if (currentTool === 'draw') elCanvasHint.textContent = drawHint;
    else elCanvasHint.textContent = general;
  }

  function setTool(tool) {
    currentTool = tool;
    connectAnchor = null;
    lineFirstPoint = null;
    if (tool !== 'draw') {
      drawStrokePageId = '';
      drawPoints = [];
      drawStrokeCtrlDown = false;
      drawCtrlMergePathId = '';
      drawCtrlMergePageId = '';
    }
    toolButtons.forEach((btn) => btn.classList.toggle('active', btn.dataset.tool === tool));
    updateCanvasHint();
    // 点击工具栏后浏览器可能尚未完成布局，立即 redraw 有时拿不到最新画布尺寸；下一帧再 resize 可立刻显示/隐藏锚点
    redraw();
    requestAnimationFrame(() => {
      resizeCanvas();
    });
  }

  toolButtons.forEach((btn) => {
    btn.addEventListener('click', () => setTool(btn.dataset.tool));
  });

  /** 删除整页及其元素，并移除涉及该页的连线；至少保留一页 */
  function deletePageById(pageId) {
    if (project.pages.length <= 1) return;
    pushUndo();
    project.edges = project.edges.filter(
      (e) => e.source.pageId !== pageId && e.target.pageId !== pageId
    );
    project.pages = project.pages.filter((pg) => pg.id !== pageId);

    if (project.activePageId === pageId) {
      project.activePageId = project.pages[0].id;
      activePageId = project.activePageId;
      loadCameraFromProject();
    }
    if (pageFrameSelectedId === pageId) pageFrameSelectedId = project.activePageId;

    if (connectAnchor && connectAnchor.pageId === pageId) connectAnchor = null;
    if (lineFirstPoint && lineFirstPoint.pageId === pageId) lineFirstPoint = null;
    if (drawStrokePageId === pageId) {
      drawStrokePageId = '';
      drawPoints = [];
    }
    if (drawCtrlMergePageId === pageId) {
      drawCtrlMergePathId = '';
      drawCtrlMergePageId = '';
    }
    if (
      moveGrabOffset &&
      (moveGrabOffset.kind === 'move-page' || moveGrabOffset.kind === 'move-node') &&
      moveGrabOffset.pageId === pageId
    ) {
      moveGrabOffset = null;
    }
    if (dragLocalStart && dragLocalStart.pageId === pageId) dragLocalStart = null;

    if (selectedNodeId && !findPageContainingNode(selectedNodeId)) selectedNodeId = null;

    resetPickCycle();
    renderPageList();
    syncPageSizeInputs();
    redraw();
    scheduleSave();
  }

  /**
   * 侧栏列表项内联改名（双击触发）
   * @param {string} pageId
   * @param {HTMLLIElement} li
   */
  function beginInlineRenamePage(pageId, li) {
    const page = findPageById(pageId);
    if (!page) return;
    const nameEl = li.querySelector('.page-list-name');
    if (!nameEl || li.querySelector('.page-rename-input')) return;

    const originalName = page.name;
    const input = document.createElement('input');
    input.type = 'text';
    input.className = 'page-rename-input';
    input.value = originalName;
    input.setAttribute('aria-label', '页面名称');

    nameEl.replaceWith(input);
    input.focus();
    input.select();

    let finished = false;

    const cleanupListeners = () => {
      input.removeEventListener('keydown', onKey);
      input.removeEventListener('blur', onBlur);
    };

    const restoreListScrollAndRender = () => {
      const st = elPageList.scrollTop;
      renderPageList();
      elPageList.scrollTop = st;
      redraw();
    };

    function finishCommit() {
      if (finished) return;
      finished = true;
      cleanupListeners();
      const next = input.value.trim();
      if (next && next !== originalName) {
        pushUndo();
        page.name = next;
        scheduleSave();
      }
      restoreListScrollAndRender();
    }

    function finishCancel() {
      if (finished) return;
      finished = true;
      cleanupListeners();
      restoreListScrollAndRender();
    }

    function onKey(ev) {
      if (ev.key === 'Enter') {
        ev.preventDefault();
        finishCommit();
      } else if (ev.key === 'Escape') {
        ev.preventDefault();
        finishCancel();
      }
    }

    function onBlur() {
      if (finished) return;
      finishCommit();
    }

    input.addEventListener('keydown', onKey);
    input.addEventListener('blur', onBlur);
  }

  function renderPageList() {
    elPageList.innerHTML = '';
    project.pages.forEach((p) => {
      const li = document.createElement('li');
      li.className = p.id === project.activePageId ? 'active' : '';

      const nameSpan = document.createElement('span');
      nameSpan.className = 'page-list-name';
      nameSpan.textContent = p.name;
      nameSpan.title = `${p.name} · 双击修改名称`;

      const btnDel = document.createElement('button');
      btnDel.type = 'button';
      btnDel.className = 'page-delete-btn';
      btnDel.textContent = '删';
      btnDel.setAttribute('aria-label', `删除页面「${p.name}」`);
      const solePage = project.pages.length <= 1;
      btnDel.disabled = solePage;
      btnDel.title = solePage ? '至少保留一页' : '删除该页面';

      li.appendChild(nameSpan);
      li.appendChild(btnDel);

      li.addEventListener('click', (ev) => {
        if (ev.target.closest('.page-delete-btn')) return;
        if (ev.target.classList.contains('page-rename-input')) return;
        syncCameraToProject();
        resetPickCycle();
        const alreadyActive = project.activePageId === p.id;
        project.activePageId = p.id;
        activePageId = p.id;
        pageFrameSelectedId = p.id;
        loadCameraFromProject();
        selectedNodeId = null;
        // 已在当前页时不要整表重绘：否则会拆掉列表 DOM，浏览器无法识别双击（第二下不在同一节点上）
        if (!alreadyActive) renderPageList();
        syncPageSizeInputs();
        redraw();
        scheduleSave();
      });

      li.addEventListener('dblclick', (ev) => {
        if (ev.target.closest('.page-delete-btn')) return;
        if (ev.target.classList.contains('page-rename-input')) return;
        ev.preventDefault();
        beginInlineRenamePage(p.id, ev.currentTarget);
      });

      btnDel.addEventListener('click', (ev) => {
        ev.stopPropagation();
        ev.preventDefault();
        if (solePage) return;
        if (!window.confirm(`确定删除页面「${p.name}」及其内容与相关连线？`)) return;
        deletePageById(p.id);
      });

      elPageList.appendChild(li);
    });
    syncPageSizeInputs();
  }

  elBtnAddPage.addEventListener('click', () => {
    syncCameraToProject();
    pushUndo();
    let maxRight = 0;
    for (const p of project.pages) {
      maxRight = Math.max(maxRight, p.x + p.width);
    }
    const dw = project.designWidth;
    const dh = project.designHeight;
    const id = newId();
    project.pages.push({
      id,
      name: '页面 ' + (project.pages.length + 1),
      x: maxRight + PAGE_GAP,
      y: 0,
      width: dw,
      height: dh,
      elements: [],
    });
    project.activePageId = id;
    activePageId = id;
    pageFrameSelectedId = id;
    selectedNodeId = null;
    resetPickCycle();
    renderPageList();
    syncPageSizeInputs();
    redraw();
    scheduleSave();
  });

  function syncFormFromProject() {
    elProjectName.value = project.name;
    elProjectWidth.value = String(project.designWidth);
    elProjectHeight.value = String(project.designHeight);
    elShowFrame.checked = !!project.showFrame;
    activePageId = project.activePageId;
    syncPageSizeInputs();
  }

  elProjectName.addEventListener('focus', () => {
    projectNameUndoPrimed = true;
  });

  elProjectName.addEventListener('input', () => {
    if (projectNameUndoPrimed && !undoRestoring) {
      pushUndo();
      projectNameUndoPrimed = false;
    }
    project.name = elProjectName.value || '未命名项目';
    scheduleSave();
  });

  function applyDesignSize() {
    pushUndo();
    project.designWidth = clampNum(parseInt(elProjectWidth.value, 10), 320, 8192, DEFAULT_WIDTH);
    project.designHeight = clampNum(parseInt(elProjectHeight.value, 10), 240, 8192, DEFAULT_HEIGHT);
    elProjectWidth.value = String(project.designWidth);
    elProjectHeight.value = String(project.designHeight);
    redraw();
    scheduleSave();
  }

  function clampNum(n, min, max, fallback) {
    if (Number.isNaN(n)) return fallback;
    return Math.min(max, Math.max(min, n));
  }

  elProjectWidth.addEventListener('change', applyDesignSize);
  elProjectHeight.addEventListener('change', applyDesignSize);

  function applyPageSize() {
    const page = getActivePage();
    if (!page) return;
    pushUndo();
    page.width = clampNum(parseInt(elPageWidth.value, 10), 320, 8192, project.designWidth);
    page.height = clampNum(parseInt(elPageHeight.value, 10), 240, 8192, project.designHeight);
    elPageWidth.value = String(page.width);
    elPageHeight.value = String(page.height);
    redraw();
    scheduleSave();
  }

  elPageWidth.addEventListener('change', applyPageSize);
  elPageHeight.addEventListener('change', applyPageSize);

  elShowFrame.addEventListener('change', () => {
    pushUndo();
    project.showFrame = elShowFrame.checked;
    redraw();
    scheduleSave();
  });

  elBtnExport.addEventListener('click', () => {
    syncCameraToProject();
    const blob = new Blob([JSON.stringify(project, null, 2)], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = (project.name || 'prototype') + '.json';
    a.click();
    URL.revokeObjectURL(a.href);
  });

  elBtnImport.addEventListener('click', () => elImportFile.click());
  elImportFile.addEventListener('change', async () => {
    const file = elImportFile.files && elImportFile.files[0];
    if (!file) return;
    try {
      const text = await file.text();
      const data = JSON.parse(text);
      // 极简校验：必须有 pages 数组
      if (!data.pages || !Array.isArray(data.pages)) throw new Error('无效的项目文件');
      project = normalizeImportedProject(data);
      clearUndoHistory();
      activePageId = project.activePageId;
      pageFrameSelectedId = project.activePageId;
      loadCameraFromProject();
      syncFormFromProject();
      renderPageList();
      selectedNodeId = null;
      redraw();
      await saveProjectToDb(project);
      elSaveStatus.textContent = '导入并已保存';
    } catch (e) {
      console.error(e);
      alert('导入失败：' + (e.message || String(e)));
    }
    elImportFile.value = '';
  });

  /**
   * 导入旧版本或缺字段时的补齐
   */
  function normalizeImportedProject(data) {
    const base = createEmptyProject();
    const merged = { ...base, ...data };
    if (!merged.pages.length) merged.pages = base.pages;
    merged.edges = Array.isArray(merged.edges) ? merged.edges : [];

    const dw = merged.designWidth ?? DEFAULT_WIDTH;
    const dh = merged.designHeight ?? DEFAULT_HEIGHT;

    if (!merged.camera || typeof merged.camera.scale !== 'number') {
      const firstCam = merged.pages[0] && merged.pages[0].camera;
      merged.camera =
        firstCam && typeof firstCam.scale === 'number'
          ? { tx: firstCam.tx, ty: firstCam.ty, scale: firstCam.scale }
          : { tx: 80, ty: 60, scale: 0.45 };
    }

    merged.pages = merged.pages.map((p, idx) => {
      const w = typeof p.width === 'number' ? p.width : dw;
      const h = typeof p.height === 'number' ? p.height : dh;
      const x = typeof p.x === 'number' ? p.x : idx * (w + PAGE_GAP);
      const y = typeof p.y === 'number' ? p.y : 0;
      return {
        id: p.id || newId(),
        name: p.name || '页面',
        x,
        y,
        width: w,
        height: h,
        elements: Array.isArray(p.elements) ? p.elements : [],
      };
    });

    const ids = new Set(merged.pages.map((p) => p.id));
    if (!ids.has(merged.activePageId)) merged.activePageId = merged.pages[0].id;
    if (typeof merged.showFrame !== 'boolean') merged.showFrame = true;

    merged.edges = merged.edges
      .filter((e) => e && e.source && e.target && e.source.pageId && e.target.pageId)
      .map((e) => ({
        id: e.id || newId(),
        source: {
          pageId: e.source.pageId,
          nodeId: e.source.nodeId == null || e.source.nodeId === '' ? null : e.source.nodeId,
        },
        target: {
          pageId: e.target.pageId,
          nodeId: e.target.nodeId == null || e.target.nodeId === '' ? null : e.target.nodeId,
        },
      }));

    return merged;
  }

  // ============================================
  // 启动：加载 → 绑定 resize → 首次绘制
  // ============================================

  async function init() {
    try {
      const saved = await loadProjectFromDb();
      if (saved) {
        project = normalizeImportedProject(saved);
      }
    } catch (e) {
      console.warn('读取本地数据库失败，使用空白项目', e);
    }

    activePageId = project.activePageId;
    pageFrameSelectedId = project.activePageId;
    clearUndoHistory();
    syncFormFromProject();
    loadCameraFromProject();
    renderPageList();
    resizeCanvas();
    window.addEventListener('resize', resizeCanvas);
    elSaveStatus.textContent = '已加载本地数据';
    updateCanvasHint();
  }

  init();
})();
