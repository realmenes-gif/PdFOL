// PdFOL para Android · visor de PDF: buscar, marcar y firmar · by Meneses999
// Usa pdf.js (dibujo, texto, busqueda y marcas) y pdf-lib (para estampar la firma al guardar).

const VERSION = "1.3";
const REPO = "realmenes-gif/PdFOL";
const CAMBIOS = [
  ["1.3", [
    "Elegir texto nuevo y suave: mantené apretado para elegir la palabra y estirá con los tiradores.",
    "Botón «Todo» para elegir el texto de toda la página.",
  ]],
  ["1.2", [
    "Copiar texto: elegí el texto (mantené apretado) y tocá «Copiar».",
    "Páginas escaneadas o fotos: PdFOL reconoce las letras y también se pueden elegir y copiar.",
  ]],
  ["1.1", [
    "Firmar ahora tiene Firmas y Sellos: hasta 5 de cada uno guardados.",
    "Firmas y sellos desde una foto o imagen: el fondo claro se quita solo y queda transparente.",
    "Lápiz con 5 plumas (bolígrafo, pluma, plumón, rotulador y fosforito), 10 colores y opacidad.",
    "Las mismas plumas, colores y opacidad para dibujar la firma.",
  ]],
  ["1.0", [
    "Primera versión para Android: visor de PDF con la misma interfaz de PdFOL.",
    "Buscar en el documento, con todas las coincidencias resaltadas.",
    "Marcar: resaltar texto, marcador libre y lápiz, con colores y grosor.",
    "Firmar: dibujá tu firma una vez, guardala y ponela donde quieras.",
    "Pestañas, miniaturas, zoom con dos dedos y doble toque.",
    "Temas Azul gris y Verde gris, claro, oscuro o automático, y modo noche para las hojas.",
  ]],
];

const AN = window.PdfolAndroid || null; // puente con Android (no existe al probar en un navegador)
const $ = (id) => document.getElementById(id);
const raiz = document.documentElement;
const esAncho = () => window.matchMedia("(min-width: 760px)").matches;
let pdfjsLib = null, V = null;

// ---------------------------------------------------------------- iconos (mismos colores que en el escritorio)
const ICO = {
  carpeta: '<path d="M3 7.5A1.5 1.5 0 0 1 4.5 6H9l2 2h8.5A1.5 1.5 0 0 1 21 9.5v8A1.5 1.5 0 0 1 19.5 19h-15A1.5 1.5 0 0 1 3 17.5z"/>',
  minis: '<rect x="4" y="4" width="7" height="7" rx="1.5"/><rect x="13" y="4" width="7" height="7" rx="1.5"/><rect x="4" y="13" width="7" height="7" rx="1.5"/><rect x="13" y="13" width="7" height="7" rx="1.5"/>',
  lupa: '<circle cx="10.5" cy="10.5" r="6"/><path d="M15 15l5 5"/>',
  marcador: '<path d="m14 5 5 5-8 8H6v-5z"/><path d="M4 21h16"/>',
  firma: '<path d="M3 17c3 0 4-9 6-9s1 8 3 8 2-4 4-4 2 3 5 3"/><path d="M3 21h18"/>',
  guardar: '<path d="M5 4h11l3 3v12a1 1 0 0 1-1 1H6a1 1 0 0 1-1-1z"/><path d="M8 4v5h7V4M8 20v-6h8v6"/>',
  compartir: '<circle cx="18" cy="5.5" r="2.5"/><circle cx="6" cy="12" r="2.5"/><circle cx="18" cy="18.5" r="2.5"/><path d="m8.2 10.8 7.6-4.1M8.2 13.2l7.6 4.1"/>',
  apariencia: '<circle cx="12" cy="12" r="8"/><path d="M12 4a8 8 0 0 0 0 16z" fill="currentColor"/>',
  mas: '<circle cx="12" cy="5" r="1.4" fill="currentColor"/><circle cx="12" cy="12" r="1.4" fill="currentColor"/><circle cx="12" cy="19" r="1.4" fill="currentColor"/>',
  pagina: '<path d="M7 3h7l5 5v13H7z"/><path d="M14 3v5h5"/>',
  ancho: '<path d="M4 12h16M7 9l-3 3 3 3M17 9l3 3-3 3"/>',
  entera: '<rect x="6" y="3" width="12" height="18" rx="1.5"/>',
  copia: '<rect x="8" y="8" width="12" height="12" rx="1.5"/><path d="M16 8V5a1 1 0 0 0-1-1H5a1 1 0 0 0-1 1v10a1 1 0 0 0 1 1h3"/>',
  luna: '<path d="M20 14.5A8 8 0 1 1 9.5 4a6.5 6.5 0 0 0 10.5 10.5z"/>',
  estrella: '<path d="m12 4 2.4 5 5.4.6-4 3.7 1.1 5.4L12 16l-4.9 2.7 1.1-5.4-4-3.7 5.4-.6z"/>',
  flecha: '<path d="M12 4v11M7 10l5 5 5-5M5 20h14"/>',
  info: '<circle cx="12" cy="12" r="9"/><path d="M12 11v6M12 7.5v.5"/>',
  cerrar: '<path d="M6 6l12 12M18 6 6 18"/>',
  doc: '<path d="M6 2.5h8l5 5V21a.5.5 0 0 1-.5.5h-12A.5.5 0 0 1 6 21z" stroke="#D32F2F"/><path d="M14 2.5v5h5" stroke="#D32F2F"/>',
};
const svg = (p, extra = "") => `<svg viewBox="0 0 24 24" ${extra}>${p}</svg>`;

const ACCIONES = [
  { k: "abrir", t: "Abrir", c: "#2563EB", i: ICO.carpeta },
  { k: "minis", t: "Miniaturas", c: "#06B6D4", i: ICO.minis, doc: true, ancho: true },
  { k: "buscar", t: "Buscar", c: "#3B82F6", i: ICO.lupa, doc: true },
  { k: "marcar", t: "Marcar", c: "#F59E0B", i: ICO.marcador, doc: true },
  { k: "firmar", t: "Firmar", c: "#8B5CF6", i: ICO.firma, doc: true },
  { k: "guardar", t: "Guardar", c: "#10B981", i: ICO.guardar, doc: true, ancho: true },
  { k: "compartir", t: "Compartir", c: "#0D9488", i: ICO.compartir, doc: true, ancho: true },
  { k: "apariencia", t: "Apariencia", c: "#64748B", i: ICO.apariencia, ancho: true },
  { k: "mas", t: "Más", i: ICO.mas },
];

const COLORES_RES = [["Amarillo", "#FFE15C"], ["Verde", "#7EE2A0"], ["Celeste", "#8FD3FF"], ["Rosa", "#FFA6D2"], ["Naranja", "#FFB566"]];
const COLORES_TINTA = [["Negro", "#1E2730"], ["Gris", "#6B7280"], ["Azul", "#1F4FB8"], ["Celeste", "#0EA5E9"], ["Rojo", "#D32F2F"],
  ["Naranja", "#F97316"], ["Amarillo", "#FACC15"], ["Verde", "#1B7F4B"], ["Morado", "#7C3AED"], ["Blanco", "#FFFFFF"]];
// plumas: grosor (puntos) y opacidad (%) de partida; despues se ajustan con los deslizadores
const PLUMAS = [
  { k: "boli", t: "Bolígrafo", grosor: 1.5, op: 100 },
  { k: "pluma", t: "Pluma", grosor: 2.5, op: 100 },
  { k: "plumon", t: "Plumón", grosor: 5, op: 100 },
  { k: "rotulador", t: "Rotulador", grosor: 9, op: 85 },
  { k: "fosforito", t: "Fosforito", grosor: 16, op: 40 },
];

// ---------------------------------------------------------------- preferencias
const PREF_DEF = { tema: "azul", modo: "auto", noche: false, minis: true, firmas: [], recientes: [], ultimaRevision: 0, colorRes: 0, grosor: 12, nuevaVersion: null, sellos: [],
  plumaLapiz: { pluma: "pluma", color: 0, grosor: 2.5, op: 100 }, plumaFirma: { pluma: "pluma", color: 0, grosor: 2, op: 100 } };
let prefs = { ...PREF_DEF };
try { prefs = { ...PREF_DEF, ...JSON.parse(localStorage.getItem("pdfol") || "{}") }; } catch (e) { /* sin almacenamiento */ }
prefs.firmas = (prefs.firmas || []).slice(0, 5);
prefs.sellos = (prefs.sellos || []).slice(0, 5);
function guardarPrefs() { try { localStorage.setItem("pdfol", JSON.stringify(prefs)); } catch (e) { /* nada */ } }

// ---------------------------------------------------------------- estado
const pest = [];        // pestanas: una por documento
let act = -1;           // pestana activa
let modo = "ver";       // ver | marcar | firma
let marcarTipo = "texto";
let uidPest = 0;
const tabAct = () => pest[act] || null;

// ---------------------------------------------------------------- tema
const mqOscuro = window.matchMedia("(prefers-color-scheme: dark)");
function esOscuro() {
  if (prefs.modo === "oscuro") return true;
  if (prefs.modo === "claro") return false;
  try { if (AN && AN.modoOscuro) return AN.modoOscuro(); } catch (e) { /* nada */ }
  return mqOscuro.matches;
}
function aplicarTema() {
  raiz.dataset.tema = prefs.tema === "verde" ? "verde" : "azul";
  if (esOscuro()) raiz.dataset.oscuro = ""; else delete raiz.dataset.oscuro;
  document.body.classList.toggle("noche", !!prefs.noche);
  const cs = getComputedStyle(raiz);
  try { AN && AN.colorBarras(cs.getPropertyValue("--lat-ini").trim(), cs.getPropertyValue("--fondo").trim(), esOscuro()); } catch (e) { /* nada */ }
}
mqOscuro.addEventListener("change", aplicarTema);
window.pdfolTemaSistema = aplicarTema; // Android avisa cuando cambia el modo oscuro del telefono

// ---------------------------------------------------------------- avisos y dialogos
let toastT = 0;
function aviso(txt, ms = 2600) {
  const t = $("toast");
  t.textContent = txt; t.hidden = false;
  clearTimeout(toastT);
  toastT = setTimeout(() => { t.hidden = true; }, ms);
}
function cerrarCapas() {
  $("menu").hidden = true; $("dialogo").hidden = true; $("velo").hidden = true;
  dialogoAbierto = null;
}
let dialogoAbierto = null;
$("velo").addEventListener("click", () => { if (dialogoAbierto?.alVelo) dialogoAbierto.alVelo(); else cerrarCapas(); });

// dialogo con botones; devuelve una promesa con la clave del boton elegido (o null)
function dialogo({ titulo, texto = "", html = "", botones = [["ok", "Aceptar", true]], alAbrir }) {
  return new Promise((resolve) => {
    const d = $("dialogo");
    d.innerHTML = `<h3></h3>${texto ? "<p></p>" : ""}<div class="cuerpo">${html}</div><div class="botones"></div>`;
    d.querySelector("h3").textContent = titulo;
    if (texto) d.querySelector("p").textContent = texto;
    const fin = (v) => { cerrarCapas(); resolve(v); };
    for (const [clave, txt, prim] of botones) {
      const b = document.createElement("button");
      b.className = prim ? "primario" : "suave";
      b.textContent = txt;
      b.onclick = () => fin(clave);
      d.querySelector(".botones").append(b);
    }
    $("menu").hidden = true;
    $("velo").hidden = false; d.hidden = false;
    dialogoAbierto = { alVelo: () => fin(null), fin };
    alAbrir?.(d, fin);
  });
}

// menu con items: [{t, i, f, der, marcado}] o "-" o {tit}
function menu(items, ancla) {
  const m = $("menu");
  m.innerHTML = "";
  for (const it of items) {
    if (it === "-") { m.insertAdjacentHTML("beforeend", '<div class="sep"></div>'); continue; }
    if (it.tit) { const t = document.createElement("div"); t.className = "tit"; t.textContent = it.tit; m.append(t); continue; }
    const b = document.createElement("button");
    b.className = "item" + (it.marcado ? " marcado" : "");
    b.innerHTML = svg(it.i || "") + "<span></span>" + (it.der ? '<span class="der"></span>' : "");
    b.children[1].textContent = it.t;
    if (it.der) b.querySelector(".der").textContent = it.der;
    b.onclick = () => { cerrarCapas(); it.f(); };
    m.append(b);
  }
  $("velo").hidden = false; m.hidden = false;
  dialogoAbierto = { alVelo: cerrarCapas };
  const r = ancla ? ancla.getBoundingClientRect() : null;
  const w = m.offsetWidth, h = m.offsetHeight;
  let x = r ? r.right - w : (innerWidth - w) / 2;
  let y = r ? r.bottom + 4 : (innerHeight - h) / 2;
  x = Math.max(8, Math.min(x, innerWidth - w - 8));
  y = Math.max(8, Math.min(y, innerHeight - h - 8));
  m.style.left = x + "px"; m.style.top = y + "px";
}

// ---------------------------------------------------------------- barra de arriba
function dibujarAcciones() {
  const nav = $("acciones");
  nav.innerHTML = "";
  const ancho = esAncho();
  const hayDoc = !!tabAct();
  for (const a of ACCIONES) {
    if (a.ancho && !ancho) continue;
    if (!ancho && a.doc && !hayDoc) continue;           // en el celular, sin documento: solo Abrir y Más
    if (!ancho && a.k === "abrir" && hayDoc) continue;   // con documento, Abrir va en «Más»
    const b = document.createElement("button");
    b.className = "accion" + (a.k === "mas" ? " mas" : "");
    b.dataset.k = a.k;
    b.setAttribute("aria-label", a.t);
    b.innerHTML = `<span class="ic" style="background:${a.c || "transparent"}">${svg(a.i)}</span><span class="et">${a.t}</span>`;
    if (a.doc && !hayDoc) b.classList.add("apagado");
    const sel = (a.k === "buscar" && !$("busqueda").hidden) || (a.k === "marcar" && modo === "marcar")
      || (a.k === "firmar" && modo === "firma") || (a.k === "minis" && !$("miniaturas").hidden);
    if (sel) b.classList.add("sel");
    b.onclick = () => accion(a.k, b);
    nav.append(b);
  }
}

function accion(k, boton) {
  switch (k) {
    case "abrir": return elegirArchivo();
    case "minis": return alternarMinis();
    case "buscar": return alternarBusqueda();
    case "marcar": return modo === "marcar" ? salirDeModo() : entrarMarcar();
    case "firmar": return modo === "firma" ? salirDeModo() : elegirFirma();
    case "guardar": return guardar();
    case "compartir": return compartir();
    case "apariencia": return dialogoApariencia();
    case "mas": return menuMas(boton);
  }
}

function menuMas(boton) {
  const t = tabAct();
  const it = [];
  it.push({ t: "Abrir PDF", i: ICO.carpeta, f: elegirArchivo });
  if (t) {
    if (!esAncho()) it.push({ t: "Miniaturas", i: ICO.minis, f: alternarMinis });
    it.push({ t: "Ir a la página…", i: ICO.pagina, f: irAPagina, der: `${t.viewer.currentPageNumber} de ${t.pdf.numPages}` });
    it.push({ t: "Ajustar al ancho", i: ICO.ancho, f: () => { t.viewer.currentScaleValue = "page-width"; } });
    it.push({ t: "Página entera", i: ICO.entera, f: () => { t.viewer.currentScaleValue = "page-fit"; } });
    it.push("-");
    it.push({ t: "Guardar", i: ICO.guardar, f: guardar, der: t.modificado ? "con cambios" : "" });
    it.push({ t: "Guardar una copia", i: ICO.copia, f: () => guardar("copia") });
    it.push({ t: "Compartir", i: ICO.compartir, f: compartir });
    it.push({ t: "Cerrar el documento", i: ICO.cerrar, f: () => cerrarPestana(act) });
    it.push("-");
  }
  it.push({ t: "Modo noche (hojas oscuras)", i: ICO.luna, marcado: prefs.noche, der: prefs.noche ? "Sí" : "No",
    f: () => { prefs.noche = !prefs.noche; guardarPrefs(); aplicarTema(); } });
  if (!esAncho()) it.push({ t: "Apariencia", i: ICO.apariencia, f: dialogoApariencia });
  it.push("-");
  it.push(...itemsHusky());
  menu(it, boton);
}

function itemsHusky() {
  return [
    { t: "Buscar actualizaciones", i: ICO.flecha, f: () => buscarActualizacion(true), der: prefs.nuevaVersion ? "¡nueva!" : "" },
    { t: "Novedades", i: ICO.estrella, f: () => verNovedades() },
    { t: "Acerca de PdFOL", i: ICO.info, f: acercaDe },
  ];
}
$("logo").onclick = () => menu([{ tit: `PdFOL v${VERSION} · by Meneses999` }, ...itemsHusky()], $("logo"));

// ---------------------------------------------------------------- pestanas
function dibujarPestanas() {
  const c = $("pestanas");
  c.innerHTML = "";
  pest.forEach((t, i) => {
    const d = document.createElement("div");
    d.className = "pest" + (i === act ? " act" : "");
    d.innerHTML = `${t.modificado ? '<span class="mod">●</span>' : ""}<span class="nom"></span><button class="x" aria-label="Cerrar">${svg(ICO.cerrar)}</button>`;
    d.querySelector(".nom").textContent = t.nombre;
    d.onclick = (e) => { if (!e.target.closest(".x")) activar(i); };
    d.querySelector(".x").onclick = () => cerrarPestana(i);
    c.append(d);
    if (i === act) requestAnimationFrame(() => d.scrollIntoView({ inline: "nearest", block: "nearest" }));
  });
  document.body.classList.toggle("con-docs", pest.length > 0);
  dibujarAcciones();
}

function activar(i) {
  if (i === act && pest[i]) return;
  limpiarSel();
  if (modo !== "ver") salirDeModo();
  pest.forEach((t, j) => { t.cont.hidden = j !== i; });
  act = i;
  const t = tabAct();
  dibujarPestanas();
  if ($("busqueda").hidden === false && t) buscar("");
  if (t) {
    actualizarIndicador();
    if (!$("miniaturas").hidden) armarMinis();
    $("zoom-fab").hidden = !esAncho();
    actualizarZoomTxt();
  } else {
    $("zoom-fab").hidden = true; $("indicador").hidden = true; $("miniaturas").hidden = true; $("velo-minis").hidden = true;
    $("busqueda").hidden = true;
  }
}

async function cerrarPestana(i, { preguntar = true } = {}) {
  const t = pest[i];
  if (!t) return;
  if (preguntar && t.modificado) {
    activar(i);
    const r = await dialogo({
      titulo: "¿Guardar los cambios?",
      texto: `«${t.nombre}» tiene marcas o firmas sin guardar.`,
      botones: [["no", "No guardar"], ["cancelar", "Cancelar"], ["si", "Guardar", true]],
    });
    if (r === null || r === "cancelar") return false;
    if (r === "si" && !(await guardar())) return false;
  }
  if (modo !== "ver" && i === act) salirDeModo();
  try { t.viewer.setDocument(null); } catch (e) { /* nada */ }
  t.pdf?.destroy();
  t.cont.remove();
  pest.splice(i, 1);
  act = -1;
  activar(Math.min(i, pest.length - 1));
  dibujarRecientes();
  return true;
}

// ---------------------------------------------------------------- abrir documentos
async function cargarLibs() {
  if (V) return;
  pdfjsLib = await import("./lib/pdf.min.mjs");
  globalThis.pdfjsLib = pdfjsLib;
  pdfjsLib.GlobalWorkerOptions.workerSrc = new URL("lib/pdf.worker.min.mjs", location.href).href;
  V = await import("./lib/pdf_viewer.min.mjs");
}

function elegirArchivo() {
  cerrarCapas();
  if (AN) AN.elegirArchivo(); else $("archivo").click();
}
$("archivo").addEventListener("change", async (e) => {
  for (const f of e.target.files) await abrirDoc({ nombre: f.name, datos: new Uint8Array(await f.arrayBuffer()) });
  e.target.value = "";
});
$("btn-abrir-grande").onclick = elegirArchivo;

// Android: documentos que llegaron (Abrir con, compartir, elegidos)
window.pdfolNativo = {
  async nuevos() {
    let lista = [];
    try { lista = JSON.parse(AN.pendientes() || "[]"); } catch (e) { /* nada */ }
    for (const d of lista) await abrirDoc({ nombre: d.nombre, idNativo: d.id, uri: d.uri, persistente: d.persistente, escribible: d.escribible });
  },
  escrito(token, ok, msg, extra) { escrituras.get(token)?.({ ok, msg, extra: extra ? JSON.parse(extra) : null }); escrituras.delete(token); },
};

const MAX_PIX = Math.min(16777216, Math.round(4096 * 4096 * Math.min(1, (window.devicePixelRatio || 1) / 2.5)) || 16777216);

async function abrirDoc(f, { reemplazar = null } = {}) {
  // si ya esta abierto, se va a su pestana
  if (!reemplazar) {
    const ya = pest.findIndex((t) => (f.uri && t.uri === f.uri) || (f.idNativo && t.idNativo === f.idNativo));
    if (ya >= 0) { activar(ya); return pest[ya]; }
  }
  await cargarLibs();
  const cont = document.createElement("div");
  cont.className = "visor";
  cont.innerHTML = '<div class="pdfViewer"></div><div class="capa-firmas"></div>';
  $("docs").append(cont);
  const eventBus = new V.EventBus();
  const linkService = new V.PDFLinkService({ eventBus });
  const findController = new V.PDFFindController({ eventBus, linkService });
  const viewer = new V.PDFViewer({
    container: cont, viewer: cont.firstElementChild, eventBus, linkService, findController,
    textLayerMode: 1, removePageBorders: true, maxCanvasPixels: MAX_PIX, enableDetailCanvas: true,
    annotationEditorMode: pdfjsLib.AnnotationEditorType.NONE,
    annotationEditorHighlightColors: COLORES_RES.map(([n, c]) => `${n.toLowerCase()}=${c}`).join(","),
    enableHighlightFloatingButton: false, supportsPinchToZoom: true, imageResourcesPath: "lib/images/",
  });
  linkService.setViewer(viewer);
  const t = {
    id: ++uidPest, nombre: f.nombre || "documento.pdf", idNativo: f.idNativo || null, uri: f.uri || null,
    escribible: f.escribible !== false, cont, eventBus, linkService, findController, viewer, pdf: null,
    firmas: [], modificado: false, editado: false, uiManager: null, pagIni: f.pagina || 1, escala: f.escala || null,
  };
  const src = {
    cMapUrl: "lib/cmaps/", cMapPacked: true, standardFontDataUrl: "lib/standard_fonts/", wasmUrl: "lib/wasm/",
    iccUrl: "lib/iccs/", useWorkerFetch: false, isEvalSupported: false, disableRange: true, enableXfa: false,
  };
  if (f.datos) src.data = f.datos;
  else src.url = new URL("/doc/" + encodeURIComponent(f.idNativo), location.href).href;
  const tarea = pdfjsLib.getDocument(src);
  tarea.onPassword = async (dar, razon) => {
    let clave = null;
    await dialogo({
      titulo: "PDF protegido",
      texto: razon === 2 ? "La contraseña no es correcta. Probá de nuevo." : `«${t.nombre}» pide una contraseña para abrirse.`,
      html: '<input type="text" id="clave" autocomplete="off" autocapitalize="off" placeholder="Contraseña">',
      botones: [["no", "Cancelar"], ["ok", "Abrir", true]],
      alAbrir: (d, fin) => {
        const i = d.querySelector("#clave"); i.focus();
        i.oninput = () => { clave = i.value; };
        i.onkeydown = (e) => { if (e.key === "Enter") fin("ok"); };
      },
    }).then((r) => { if (r === "ok") dar(clave || ""); else tarea.destroy(); });
  };
  try {
    t.pdf = await tarea.promise;
  } catch (e) {
    cont.remove();
    if (!/destroy/i.test(String(e))) aviso(`No se pudo abrir «${t.nombre}».`);
    return null;
  }
  conectarEventos(t);
  viewer.setDocument(t.pdf);
  linkService.setDocument(t.pdf);
  t.pdf.annotationStorage.onSetModified = () => { t.editado = true; marcarModificado(t, true); };
  if (reemplazar) {
    const i = pest.indexOf(reemplazar);
    try { reemplazar.viewer.setDocument(null); } catch (e) { /* nada */ }
    reemplazar.pdf?.destroy(); reemplazar.cont.remove();
    pest[i] = t; act = -1; activar(i);
  } else {
    pest.push(t);
    activar(pest.length - 1);
    if (esAncho() && prefs.minis && $("miniaturas").hidden) { alternarMinis(); prefs.minis = true; }
  }
  if (f.persistente && f.uri) anotarReciente(t.nombre, f.uri);
  armarGestos(t);
  armarSeleccion(t);
  return t;
}

function conectarEventos(t) {
  const { eventBus, viewer } = t;
  eventBus.on("pagesinit", () => {
    viewer.currentScaleValue = t.escala || (esAncho() ? "auto" : "page-width");
    if (t.pagIni > 1) viewer.currentPageNumber = Math.min(t.pagIni, t.pdf.numPages);
    actualizarIndicador(); actualizarZoomTxt();
  });
  eventBus.on("pagechanging", () => { if (t === tabAct()) { actualizarIndicador(true); marcarMiniAct(); } });
  eventBus.on("scalechanging", () => { if (t === tabAct()) actualizarZoomTxt(); ubicarFirmas(t); if (sel?.t === t) requestAnimationFrame(dibujarSel); });
  eventBus.on("updateviewarea", () => ubicarFirmas(t));
  eventBus.on("pagerendered", () => ubicarFirmas(t));
  eventBus.on("textlayerrendered", (e) => revisarTextoPagina(t, e.pageNumber));
  eventBus.on("updatefindmatchescount", (e) => cuentaBusqueda(t, e.matchesCount));
  eventBus.on("updatefindcontrolstate", (e) => cuentaBusqueda(t, e.matchesCount, e.state));
  eventBus.on("annotationeditoruimanager", (e) => { t.uiManager = e.uiManager; });
  eventBus.on("showannotationeditorui", (e) => { viewer.annotationEditorMode = { mode: e.mode }; });
  eventBus.on("switchannotationeditormode", (e) => { viewer.annotationEditorMode = { mode: e.mode }; });
  eventBus.on("annotationeditorstateschanged", (e) => {
    const d = e.details || {};
    if ("hasSomethingToUndo" in d) $("m-deshacer").disabled = !d.hasSomethingToUndo;
    if ("hasSomethingToRedo" in d) $("m-rehacer").disabled = !d.hasSomethingToRedo;
    if ("hasSelectedEditor" in d) $("m-borrar").disabled = !d.hasSelectedEditor;
  });
  let tScroll = 0;
  t.cont.addEventListener("scroll", () => {
    if (t !== tabAct()) return;
    actualizarIndicador(true);
    clearTimeout(tScroll);
    tScroll = setTimeout(() => $("indicador").classList.add("oculto"), 1400);
  }, { passive: true });
}

function marcarModificado(t, si) {
  if (t.modificado === si) return;
  t.modificado = si;
  dibujarPestanas();
}

// ---------------------------------------------------------------- indicador de pagina y zoom
function actualizarIndicador(mostrar) {
  const t = tabAct();
  const ind = $("indicador");
  if (!t || !t.pdf) { ind.hidden = true; return; }
  ind.hidden = false;
  $("ind-txt").textContent = `${t.viewer.currentPageNumber} / ${t.pdf.numPages}`;
  if (mostrar) ind.classList.remove("oculto");
}
$("indicador").onclick = () => irAPagina();
function actualizarZoomTxt() {
  const t = tabAct();
  if (t) $("z-val").textContent = Math.round(t.viewer.currentScale * 100) + " %";
}
$("z-mas").onclick = () => tabAct()?.viewer.increaseScale();
$("z-menos").onclick = () => tabAct()?.viewer.decreaseScale();
$("z-val").onclick = (e) => {
  const t = tabAct(); if (!t) return;
  menu([
    { t: "Ajustar al ancho", i: ICO.ancho, f: () => { t.viewer.currentScaleValue = "page-width"; } },
    { t: "Página entera", i: ICO.entera, f: () => { t.viewer.currentScaleValue = "page-fit"; } },
    ...[50, 75, 100, 150, 200, 300].map((z) => ({ t: z + " %", f: () => { t.viewer.currentScaleValue = String(z / 100); } })),
  ], e.currentTarget);
};

async function irAPagina() {
  const t = tabAct(); if (!t) return;
  let v = "";
  const r = await dialogo({
    titulo: "Ir a la página",
    texto: `El documento tiene ${t.pdf.numPages} páginas.`,
    html: `<input type="number" id="nro" min="1" max="${t.pdf.numPages}" inputmode="numeric" placeholder="${t.viewer.currentPageNumber}">`,
    botones: [["no", "Cancelar"], ["ok", "Ir", true]],
    alAbrir: (d, fin) => {
      const i = d.querySelector("#nro"); setTimeout(() => i.focus(), 50);
      i.oninput = () => { v = i.value; };
      i.onkeydown = (e) => { if (e.key === "Enter") fin("ok"); };
    },
  });
  const n = parseInt(v, 10);
  if (r === "ok" && n >= 1 && n <= t.pdf.numPages) t.viewer.currentPageNumber = n;
}

// ---------------------------------------------------------------- gestos: pellizcar, doble toque y dos dedos
function armarGestos(t) {
  const c = t.cont;
  let pinza = null, toque = null;
  const dist = (a, b) => Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
  const centro = (a, b) => [(a.clientX + b.clientX) / 2, (a.clientY + b.clientY) / 2];
  c.addEventListener("touchstart", (e) => {
    if (e.touches.length === 2) {
      const [a, b] = e.touches;
      pinza = { d0: dist(a, b), esc0: t.viewer.currentScale, c0: centro(a, b) };
      e.preventDefault();
    } else if (e.touches.length === 1) {
      const p = e.touches[0];
      const ahora = Date.now();
      if (modo === "ver" && toque && ahora - toque.t < 300 && Math.hypot(p.clientX - toque.x, p.clientY - toque.y) < 30) {
        e.preventDefault();
        dobleToque(t, p.clientX, p.clientY);
        toque = null;
      } else {
        toque = { t: ahora, x: p.clientX, y: p.clientY };
      }
    }
  }, { passive: false });
  c.addEventListener("touchmove", (e) => {
    if (!pinza || e.touches.length !== 2) return;
    e.preventDefault();
    const [a, b] = e.touches;
    const cen = centro(a, b);
    // dos dedos tambien mueven la hoja (sirve mientras se marca o se dibuja)
    c.scrollLeft -= cen[0] - pinza.c0[0];
    c.scrollTop -= cen[1] - pinza.c0[1];
    pinza.c0 = cen;
    const objetivo = Math.min(10, Math.max(0.25, pinza.esc0 * dist(a, b) / pinza.d0));
    const f = objetivo / t.viewer.currentScale;
    if (Math.abs(f - 1) > 0.015) t.viewer.updateScale({ scaleFactor: f, origin: cen, drawingDelay: 350 });
  }, { passive: false });
  c.addEventListener("touchend", (e) => { if (e.touches.length < 2) pinza = null; });
  c.addEventListener("touchcancel", () => { pinza = null; });
  // con mouse (tablet con teclado o navegador): Ctrl + rueda
  c.addEventListener("wheel", (e) => {
    if (!e.ctrlKey) return;
    e.preventDefault();
    t.viewer.updateScale({ scaleFactor: e.deltaY < 0 ? 1.1 : 1 / 1.1, origin: [e.clientX, e.clientY], drawingDelay: 250 });
  }, { passive: false });
  c.addEventListener("dblclick", (e) => { if (modo === "ver" && !e.target.closest(".textLayer span")) dobleToque(t, e.clientX, e.clientY); });
}
function dobleToque(t, x, y) {
  const v = t.viewer;
  const pv = v.getPageView(v.currentPageNumber - 1);
  const anchoPag = pv ? pv.viewport.width / v.currentScale : 600;
  const ajuste = (t.cont.clientWidth - 16) / anchoPag;
  if (v.currentScale < ajuste * 1.6) v.updateScale({ scaleFactor: (ajuste * 2.2) / v.currentScale, origin: [x, y] });
  else v.currentScaleValue = "page-width";
}

// ---------------------------------------------------------------- miniaturas
let obsMinis = null;
function alternarMinis() {
  const m = $("miniaturas");
  if (m.hidden) {
    m.hidden = false;
    if (!esAncho()) $("velo-minis").hidden = false;
    armarMinis();
  } else {
    m.hidden = true; $("velo-minis").hidden = true;
  }
  if (esAncho()) { prefs.minis = !m.hidden; guardarPrefs(); }
  dibujarAcciones();
}
$("velo-minis").onclick = alternarMinis;
function armarMinis() {
  const t = tabAct();
  const c = $("minis");
  if (!t || !t.pdf) { c.innerHTML = ""; return; }
  if (c.dataset.tab === String(t.id)) { marcarMiniAct(true); return; }
  c.dataset.tab = String(t.id);
  c.innerHTML = "";
  obsMinis?.disconnect();
  obsMinis = new IntersectionObserver((ents) => {
    for (const en of ents) if (en.isIntersecting) { dibujarMini(t, en.target); obsMinis.unobserve(en.target); }
  }, { root: $("miniaturas"), rootMargin: "300px" });
  const pv = t.viewer.getPageView(0);
  const prop = pv ? pv.viewport.height / pv.viewport.width : 1.414;
  for (let i = 1; i <= t.pdf.numPages; i++) {
    const d = document.createElement("button");
    d.className = "mini";
    d.dataset.n = i;
    const w = 96, h = Math.round(w * prop);
    d.innerHTML = `<div class="hoja" style="width:${w}px;height:${h}px"></div><span>${i}</span>`;
    d.onclick = () => {
      t.viewer.currentPageNumber = i;
      if (!esAncho()) alternarMinis();
    };
    c.append(d);
    obsMinis.observe(d);
  }
  marcarMiniAct(true);
}
async function dibujarMini(t, el) {
  try {
    const pag = await t.pdf.getPage(+el.dataset.n);
    const vp1 = pag.getViewport({ scale: 1 });
    const esc = (110 * Math.min(2, window.devicePixelRatio || 1)) / vp1.width;
    const vp = pag.getViewport({ scale: esc });
    const cv = document.createElement("canvas");
    cv.width = Math.round(vp.width); cv.height = Math.round(vp.height);
    await pag.render({ canvas: cv, canvasContext: cv.getContext("2d"), viewport: vp }).promise;
    const hoja = el.querySelector(".hoja");
    hoja.style.height = Math.round(96 * vp.height / vp.width) + "px";
    hoja.append(cv);
  } catch (e) { /* pagina dañada: queda en blanco */ }
}
function marcarMiniAct(desplazar) {
  const t = tabAct();
  if (!t || $("miniaturas").hidden) return;
  const n = t.viewer.currentPageNumber;
  for (const m of $("minis").children) m.classList.toggle("act", +m.dataset.n === n);
  const a = $("minis").querySelector(".mini.act");
  if (a && desplazar !== false) a.scrollIntoView({ block: "nearest" });
}

// ---------------------------------------------------------------- busqueda
function alternarBusqueda() {
  const b = $("busqueda");
  if (b.hidden) {
    b.hidden = false;
    $("q").focus(); $("q").select();
    if ($("q").value) buscar("");
  } else cerrarBusqueda();
  dibujarAcciones();
}
function cerrarBusqueda() {
  $("busqueda").hidden = true;
  $("q").blur();
  for (const t of pest) t.eventBus.dispatch("findbarclose", { source: window });
  $("q-cuenta").textContent = "";
  dibujarAcciones();
}
function buscar(tipo, previo = false) {
  const t = tabAct();
  if (!t) return;
  const q = $("q").value;
  if (!q) { t.eventBus.dispatch("findbarclose", { source: window }); $("q-cuenta").textContent = ""; return; }
  t.eventBus.dispatch("find", {
    source: window, type: tipo, query: q, caseSensitive: false, entireWord: false,
    highlightAll: true, findPrevious: previo, matchDiacritics: false,
  });
}
let tBusq = 0;
$("q").addEventListener("input", () => { clearTimeout(tBusq); tBusq = setTimeout(() => buscar(""), 280); });
$("q").addEventListener("keydown", (e) => {
  if (e.key === "Enter") { e.preventDefault(); buscar("again", e.shiftKey); $("q").blur(); }
  if (e.key === "Escape") cerrarBusqueda();
});
$("q-sig").onclick = () => buscar("again", false);
$("q-ant").onclick = () => buscar("again", true);
$("q-cerrar").onclick = cerrarBusqueda;
function cuentaBusqueda(t, mc, estado) {
  if (t !== tabAct()) return;
  if (estado === 1) { $("q-cuenta").textContent = "Sin resultados"; return; }
  if (mc && mc.total) $("q-cuenta").textContent = `${mc.current || 0} de ${mc.total}`;
  else if (estado === 3) $("q-cuenta").textContent = "…";
}

// ---------------------------------------------------------------- marcar (resaltar texto, marcador libre, lapiz)
function entrarMarcar() {
  if (!tabAct()) return;
  if (modo === "firma") salirDeModo();
  modo = "marcar";
  $("herr-marcar").hidden = false;
  ponerTipoMarca(marcarTipo);
  dibujarAcciones();
}
function salirDeModo() {
  const t = tabAct();
  if (modo === "marcar" && t) {
    try { t.viewer.annotationEditorMode = { mode: pdfjsLib.AnnotationEditorType.NONE }; } catch (e) { /* nada */ }
    t.cont.classList.remove("dibujando", "libre");
  }
  if (modo === "firma" && t) editarFirma(t, null);
  modo = "ver";
  $("herr-marcar").hidden = true; $("herr-firma").hidden = true;
  $("btn-res-sel")?.remove();
  dibujarAcciones();
}
function ponerTipoMarca(tipo) {
  const t = tabAct();
  if (!t) return;
  marcarTipo = tipo;
  for (const b of $("seg-marcar").children) b.classList.toggle("sel", b.dataset.m === tipo);
  const T = pdfjsLib.AnnotationEditorType, P = pdfjsLib.AnnotationEditorParamsType;
  const modoPdf = tipo === "lapiz" ? T.INK : tipo === "libre" ? T.HIGHLIGHT : T.NONE;
  try { t.viewer.annotationEditorMode = { mode: modoPdf }; } catch (e) { /* nada */ }
  t.cont.classList.toggle("dibujando", tipo !== "texto");
  t.cont.classList.toggle("libre", tipo === "libre");
  $("ayuda-marcar").textContent = tipo === "texto"
    ? "Mantené apretado sobre el texto, ajustá la selección y tocá «Resaltar»."
    : tipo === "libre" ? "Pasá el dedo sobre la hoja para marcar. Con dos dedos movés la hoja."
      : "Dibujá con el dedo. Con dos dedos movés y hacés zoom.";
  dibujarColores();
  aplicarParams();
}
for (const b of $("seg-marcar").children) b.onclick = () => ponerTipoMarca(b.dataset.m);
function dibujarColores() {
  const lapiz = marcarTipo === "lapiz";
  $("lapiz-opc").hidden = !lapiz;
  $("fila-res").hidden = lapiz;
  if (lapiz) {
    if (!$("lapiz-opc").firstChild) {
      $("lapiz-opc").innerHTML = htmlPlumas("pl");
      armarPlumas($("lapiz-opc"), "pl", prefs.plumaLapiz, () => { guardarPrefs(); aplicarParams(); });
    }
    return;
  }
  const c = $("colores");
  c.innerHTML = "";
  COLORES_RES.forEach(([n, col], i) => {
    const b = document.createElement("button");
    b.className = "color" + (i === prefs.colorRes ? " sel" : "");
    b.style.background = col;
    b.setAttribute("aria-label", n);
    b.onclick = () => { prefs.colorRes = i; guardarPrefs(); dibujarColores(); aplicarParams(); };
    c.append(b);
  });
  $("grosor").parentElement.hidden = marcarTipo === "texto";
  $("grosor").value = prefs.grosor;
}
$("grosor").oninput = () => { prefs.grosor = +$("grosor").value; guardarPrefs(); aplicarParams(); };
function aplicarParams() {
  const t = tabAct();
  if (!t) return;
  const P = pdfjsLib.AnnotationEditorParamsType;
  const disp = (type, value) => t.eventBus.dispatch("switchannotationeditorparams", { source: window, type, value });
  // se aplica cuando el editor ya existe (despues de cambiar de modo)
  setTimeout(() => {
    if (marcarTipo === "lapiz") {
      const pl = prefs.plumaLapiz;
      disp(P.INK_COLOR, COLORES_TINTA[pl.color]?.[1] || "#1E2730");
      disp(P.INK_THICKNESS, pl.grosor);
      disp(P.INK_OPACITY, pl.op / 100);
    } else {
      disp(P.HIGHLIGHT_COLOR, COLORES_RES[prefs.colorRes]?.[1] || "#FFE15C");
      disp(P.HIGHLIGHT_THICKNESS, prefs.grosor);
    }
  }, 60);
}
const accionEditor = (name) => tabAct()?.eventBus.dispatch("editingaction", { source: window, name });
$("m-deshacer").onclick = () => accionEditor("undo");
$("m-rehacer").onclick = () => accionEditor("redo");
$("m-borrar").onclick = () => accionEditor("delete");
$("m-listo").onclick = salirDeModo;

// ---------------------------------------------------------------- elegir texto (propio, suave en pantallas tactiles)
// Mantener apretado elige la palabra; despues se estira con los dos tiradores. Funciona igual con el texto del PDF
// y con el reconocido de una imagen (OCR). La seleccion del navegador no se usa: en el celular salta de lado a lado.
let sel = null; // {t, n, s, e, idx}
const indices = new WeakMap(); // capa de texto -> indice de letras

function indiceDePagina(t, n) {
  const pv = t.viewer.getPageView(n - 1);
  const capa = pv?.textLayer?.div;
  if (!capa) return null;
  const spans = [...capa.querySelectorAll("span")].filter((s) => s.firstChild?.nodeType === 3 && s.getAttribute("role") !== "img");
  const prev = indices.get(capa);
  if (prev && prev.cuantos === spans.length) return prev;
  const pr = pv.div.getBoundingClientRect();
  if (!pr.width) return null;
  const letras = [];
  const rg = document.createRange();
  for (const sp of spans) {
    const nodo = sp.firstChild, txt = nodo.textContent;
    for (let i = 0; i < txt.length; i++) {
      rg.setStart(nodo, i); rg.setEnd(nodo, i + 1);
      const r = rg.getBoundingClientRect();
      if (!r.width && !r.height) continue;
      letras.push({ nodo, i, c: txt[i], x0: (r.left - pr.left) / pr.width, x1: (r.right - pr.left) / pr.width,
        y0: (r.top - pr.top) / pr.height, y1: (r.bottom - pr.top) / pr.height, sp });
    }
  }
  // renglones: letras seguidas a la misma altura
  const lineas = [];
  let cur = null;
  letras.forEach((l, k) => {
    const cy = (l.y0 + l.y1) / 2, h = l.y1 - l.y0;
    if (!cur || Math.abs(cy - cur.cy) > 0.55 * Math.max(h, cur.h) || (l.x0 < cur.x1 - 0.02 && l.sp !== letras[k - 1].sp)) {
      cur = { cy, h, y0: l.y0, y1: l.y1, x1: l.x1, desde: k, hasta: k };
      lineas.push(cur);
    } else {
      cur.hasta = k; cur.y0 = Math.min(cur.y0, l.y0); cur.y1 = Math.max(cur.y1, l.y1); cur.x1 = Math.max(cur.x1, l.x1);
    }
    l.linea = lineas.length - 1;
  });
  const idx = { cuantos: spans.length, letras, lineas };
  indices.set(capa, idx);
  return idx;
}

// pagina y punto (en fracciones de la pagina) debajo de un punto de la pantalla
function paginaEnPunto(t, x, y) {
  for (const pv of t.viewer._pages || []) {
    const r = pv.div.getBoundingClientRect();
    if (y >= r.top && y <= r.bottom && x >= r.left - 20 && x <= r.right + 20) return { n: pv.id, fx: (x - r.left) / r.width, fy: (y - r.top) / r.height, r };
  }
  return null;
}
// renglon mas cercano en vertical y, dentro de el, el borde entre letras mas cercano (0..letras.length)
function bordeCercano(idx, fx, fy) {
  let mejor = null, dmin = Infinity;
  idx.lineas.forEach((ln) => {
    const d = fy < ln.y0 ? ln.y0 - fy : fy > ln.y1 ? fy - ln.y1 : 0;
    if (d < dmin) { dmin = d; mejor = ln; }
  });
  if (!mejor) return null;
  let k = mejor.desde, dx = Infinity;
  for (let j = mejor.desde; j <= mejor.hasta; j++) {
    const l = idx.letras[j];
    const a = Math.abs(fx - l.x0);
    if (a < dx) { dx = a; k = j; }
    if (j === mejor.hasta && Math.abs(fx - l.x1) < dx) { dx = Math.abs(fx - l.x1); k = j + 1; }
  }
  return k;
}
function palabraEn(idx, fx, fy) {
  let k = -1, dmin = Infinity;
  idx.letras.forEach((l, j) => {
    const dx = fx < l.x0 ? l.x0 - fx : fx > l.x1 ? fx - l.x1 : 0, dy = fy < l.y0 ? l.y0 - fy : fy > l.y1 ? fy - l.y1 : 0;
    const d = dx * dx + dy * dy * 4;
    if (d < dmin) { dmin = d; k = j; }
  });
  if (k < 0 || dmin > 0.0016) return null;
  const L = idx.letras, esLetra = (j) => L[j] && L[j].linea === L[k].linea && /[\p{L}\p{N}@._\-/:%$#°ºª]/u.test(L[j].c);
  if (!esLetra(k)) return [k, k + 1];
  let s = k, e = k + 1;
  while (esLetra(s - 1)) s--;
  while (esLetra(e)) e++;
  return [s, e];
}

function textoDeSel() {
  if (!sel) return "";
  const L = sel.idx.letras;
  let out = "", linea = null;
  for (let j = sel.s; j < sel.e; j++) {
    const l = L[j];
    if (linea !== null && l.linea !== linea) out = out.replace(/ +$/, "") + "\n";
    else if (linea !== null && l.sp !== L[j - 1].sp && !/\s$/.test(out) && l.x0 - L[j - 1].x1 > 0.004) out += " ";
    out += l.c;
    linea = l.linea;
  }
  return out.replace(/[ \t]+\n/g, "\n").trim();
}

function capaSel(t) {
  let c = t.cont.querySelector(".capa-sel");
  if (!c) { c = document.createElement("div"); c.className = "capa-sel"; t.cont.append(c); }
  return c;
}
function dibujarSel(arrastrado = null) {
  for (const t of pest) if (!sel || sel.t !== t) t.cont.querySelector(".capa-sel")?.replaceChildren();
  if (!sel) { $("btn-res-sel")?.remove(); return; }
  const { t, n, s, e, idx } = sel;
  const pv = t.viewer.getPageView(n - 1);
  const d = pv.div, W = d.offsetWidth, H = d.offsetHeight, ox = d.offsetLeft, oy = d.offsetTop;
  const capa = capaSel(t);
  for (const ch of [...capa.children]) if (ch !== arrastrado) ch.remove();
  const porLinea = new Map();
  for (let j = s; j < e; j++) {
    const l = idx.letras[j];
    const r = porLinea.get(l.linea) || { x0: 1, x1: 0 };
    r.x0 = Math.min(r.x0, l.x0); r.x1 = Math.max(r.x1, l.x1);
    porLinea.set(l.linea, r);
  }
  for (const [ln, r] of porLinea) {
    const L = idx.lineas[ln];
    const div = document.createElement("div");
    div.className = "sel-rect";
    Object.assign(div.style, { left: ox + r.x0 * W + "px", top: oy + L.y0 * H + "px", width: (r.x1 - r.x0) * W + "px", height: (L.y1 - L.y0) * H + "px" });
    capa.append(div);
  }
  const a = idx.letras[s], b = idx.letras[e - 1];
  const la = idx.lineas[a.linea], lb = idx.lineas[b.linea];
  for (const [cual, x, y] of [["ini", a.x0, la.y1], ["fin", b.x1, lb.y1]]) {
    if (arrastrado && arrastrado.dataset.cual === cual) {
      Object.assign(arrastrado.style, { left: ox + x * W + "px", top: oy + y * H + "px" });
      arrastrado.className = "sel-tirador arrastrando " + cual;
      continue;
    }
    const h = document.createElement("div");
    h.className = "sel-tirador " + cual;
    h.dataset.cual = cual;
    Object.assign(h.style, { left: ox + x * W + "px", top: oy + y * H + "px" });
    capa.append(h);
    tirador(h);
  }
  mostrarBarraSel();
}
function tirador(h) {
  let ini = null;
  h.addEventListener("pointerdown", (ev) => {
    ev.preventDefault(); ev.stopPropagation();
    h.setPointerCapture(ev.pointerId);
    const r = h.getBoundingClientRect();
    ini = { dx: ev.clientX - (r.left + r.width / 2), dy: ev.clientY - r.top };
    h.classList.add("arrastrando");
  });
  h.addEventListener("pointermove", (ev) => {
    if (!ini || !sel) return;
    const { t, n, idx } = sel;
    const pv = t.viewer.getPageView(n - 1), pr = pv.div.getBoundingClientRect();
    const cr = t.cont.getBoundingClientRect();
    if (ev.clientY < cr.top + 48) t.cont.scrollTop -= 10; // cerca del borde: la hoja se mueve sola
    else if (ev.clientY > cr.bottom - 48) t.cont.scrollTop += 10;
    // el punto que se busca es la base del renglon, arriba del dedo
    const ln = idx.lineas[idx.letras[h.dataset.cual === "ini" ? sel.s : sel.e - 1].linea];
    const px = (ev.clientX - ini.dx - pr.left) / pr.width;
    const py = (ev.clientY - ini.dy - pr.top) / pr.height - (ln.y1 - ln.y0) / 2;
    const k = bordeCercano(idx, px, py);
    if (k === null) return;
    if (h.dataset.cual === "ini") {
      if (k < sel.e) sel.s = k; else { sel.s = sel.e - 1; sel.e = k; h.dataset.cual = "fin"; }
    } else if (k > sel.s) sel.e = k; else { sel.e = sel.s + 1; sel.s = k; h.dataset.cual = "ini"; }
    if (sel.e <= sel.s) sel.e = sel.s + 1;
    dibujarSel(h); // el tirador que se arrastra sigue siendo el mismo (no pierde el dedo)
  });
  const fin = () => { ini = null; h.classList.remove("arrastrando"); if (sel) dibujarSel(); };
  h.addEventListener("pointerup", fin);
  h.addEventListener("pointercancel", fin);
}
function limpiarSel() {
  if (!sel) return;
  sel = null;
  dibujarSel();
}

// mantener apretado sobre el texto: elige la palabra
function armarSeleccion(t) {
  const c = t.cont;
  let toque = null;
  c.addEventListener("contextmenu", (e) => e.preventDefault());
  c.addEventListener("pointerdown", (e) => {
    if (e.target.closest(".sel-tirador, .firma-en-pag, .annotationEditorLayer .selectedEditor")) return;
    if (!e.isPrimary || (modo === "marcar" && marcarTipo !== "texto") || modo === "firma") return;
    const x = e.clientX, y = e.clientY;
    clearTimeout(toque?.timer);
    toque = { x, y, movio: false, timer: setTimeout(() => elegirPalabra(t, x, y), e.pointerType === "mouse" ? 600 : 450) };
  });
  c.addEventListener("pointermove", (e) => {
    if (toque && Math.hypot(e.clientX - toque.x, e.clientY - toque.y) > 10) { toque.movio = true; clearTimeout(toque.timer); }
  });
  const soltar = (e) => {
    if (!toque) return;
    clearTimeout(toque.timer);
    // un toque corto fuera de la seleccion la quita
    if (!toque.movio && !toque.largo && e.type === "pointerup" && sel && !e.target.closest(".sel-tirador, .barra-sel")) limpiarSel();
    toque = null;
  };
  c.addEventListener("pointerup", soltar);
  c.addEventListener("pointercancel", (e) => { if (toque) { clearTimeout(toque.timer); toque = null; } });
  c.addEventListener("scroll", () => { if (toque) { clearTimeout(toque.timer); toque.movio = true; } }, { passive: true });
  function elegirPalabra(t_, x, y) {
    if (toque) toque.largo = true;
    const p = paginaEnPunto(t_, x, y);
    if (!p) return;
    const idx = indiceDePagina(t_, p.n);
    if (!idx || !idx.letras.length) {
      if (t_.ocr?.[p.n] === "cola" || ocrTrabajando) aviso("Todavía se está reconociendo el texto de esta página…");
      return;
    }
    const w = palabraEn(idx, p.fx, p.fy);
    if (!w) { limpiarSel(); return; }
    try { navigator.vibrate?.(12); } catch (e) { /* nada */ }
    sel = { t: t_, n: p.n, s: w[0], e: w[1], idx };
    dibujarSel();
  }
}

// botones «Copiar» y «Resaltar» mientras hay texto elegido
function mostrarBarraSel() {
  let b = $("btn-res-sel");
  if (!b) {
    b = document.createElement("div");
    b.id = "btn-res-sel";
    b.className = "barra-sel";
    b.innerHTML = `<button class="suave" id="sel-todo">Todo</button><button class="suave" id="sel-copiar">${svg(ICO.copia)}Copiar</button><button class="primario" id="sel-resaltar">${svg(ICO.marcador)}Resaltar</button>`;
    b.querySelector("#sel-copiar").onclick = copiarSeleccion;
    b.querySelector("#sel-resaltar").onclick = resaltarSeleccion;
    b.querySelector("#sel-todo").onclick = () => { if (sel) { sel.s = 0; sel.e = sel.idx.letras.length; dibujarSel(); } };
    document.body.append(b);
  }
  const abajo = $("herr-marcar").hidden ? 70 : $("herr-marcar").offsetHeight + 16;
  b.style.bottom = abajo + "px";
}
async function copiarSeleccion() {
  const txt = textoDeSel();
  if (!txt) return;
  let ok = false;
  try { if (AN && AN.copiar) { AN.copiar(txt); ok = true; } } catch (e) { /* nada */ }
  if (!ok) { try { await navigator.clipboard.writeText(txt); ok = true; } catch (e) { ok = false; } }
  limpiarSel();
  aviso(ok ? "Texto copiado." : "No se pudo copiar.");
}

// ---------------------------------------------------------------- reconocer texto en paginas escaneadas (OCR)
// Si una pagina no trae texto (foto o escaneo), Android reconoce los caracteres y se agrega una capa de texto
// invisible: asi se puede elegir y copiar igual que en un PDF con texto.
const ocrCola = [];
let ocrTrabajando = false, ocrAvisado = false;
const ocrPend = new Map();
window.pdfolNativo.ocrListo = (token, json) => { ocrPend.get(token)?.(json); ocrPend.delete(token); };
const ocrDisponible = () => !!(AN && AN.ocr) || !!window._ocrPrueba;

function revisarTextoPagina(t, n) {
  if (!ocrDisponible()) return;
  t.ocr ||= {};
  const pv = t.viewer.getPageView(n - 1);
  const capa = pv?.textLayer?.div;
  if (!capa) return;
  if (Array.isArray(t.ocr[n])) { ponerCapaOcr(t, n); return; }
  if (t.ocr[n]) return; // en cola, trabajando o sin resultado
  const propio = [...capa.querySelectorAll("span:not(.ocr)")].map((x) => x.textContent).join("").replace(/\s/g, "");
  if (propio.length >= 15) { t.ocr[n] = "texto"; return; }
  t.ocr[n] = "cola";
  ocrCola.push([t, n]);
  siguienteOcr();
}

async function siguienteOcr() {
  if (ocrTrabajando) return;
  // primero las paginas que se estan viendo
  const t0 = tabAct();
  let i = ocrCola.findIndex(([t, n]) => t === t0 && Math.abs(n - t.viewer.currentPageNumber) <= 1);
  if (i < 0) i = ocrCola.findIndex(([t]) => pest.includes(t));
  if (i < 0) { ocrCola.length = 0; return; }
  const [t, n] = ocrCola.splice(i, 1)[0];
  if (!pest.includes(t)) { siguienteOcr(); return; }
  ocrTrabajando = true;
  const chip = $("chip-ocr");
  chip.textContent = `Reconociendo texto · pág. ${n}`;
  chip.hidden = t !== tabAct();
  try {
    const r = await reconocerPagina(t, n);
    if (r?.error === "descargando") {
      t.ocr[n] = null; // se reintenta despues
      aviso("Preparando el reconocimiento de texto (la primera vez necesita internet)…", 4000);
      setTimeout(() => revisarTextoPagina(t, n), 8000);
    } else {
      t.ocr[n] = r?.lineas || [];
      console.info(`PdFOL OCR pag ${n}: ${t.ocr[n].length} lineas` + (r?.error ? ` (error ${r.error})` : ""));
      ponerCapaOcr(t, n);
      if (t.ocr[n].length && !ocrAvisado) { ocrAvisado = true; aviso("Texto reconocido: mantené apretado para elegirlo y copiarlo."); }
    }
  } catch (e) {
    t.ocr[n] = "error";
  }
  chip.hidden = true;
  ocrTrabajando = false;
  if (ocrCola.length) setTimeout(siguienteOcr, 50);
}

async function reconocerPagina(t, n) {
  const pag = await t.pdf.getPage(n);
  const vp1 = pag.getViewport({ scale: 1 });
  const esc = Math.min(4, 2400 / Math.max(vp1.width, vp1.height));
  const vp = pag.getViewport({ scale: esc });
  const cv = document.createElement("canvas");
  cv.width = Math.round(vp.width); cv.height = Math.round(vp.height);
  const ctx = cv.getContext("2d");
  ctx.fillStyle = "#fff"; ctx.fillRect(0, 0, cv.width, cv.height);
  await pag.render({ canvas: cv, canvasContext: ctx, viewport: vp, annotationMode: pdfjsLib.AnnotationMode.DISABLE }).promise;
  const jpg = cv.toDataURL("image/jpeg", 0.9);
  cv.width = cv.height = 0;
  const datos = await new Promise((resolve) => {
    if (window._ocrPrueba) { window._ocrPrueba(jpg).then(resolve); return; }
    const token = "o" + Date.now() + Math.random().toString(36).slice(2, 7);
    ocrPend.set(token, (json) => { try { resolve(JSON.parse(json)); } catch (e) { resolve(null); } });
    AN.ocr(token, jpg.slice(jpg.indexOf(",") + 1));
  });
  if (!datos || datos.error) return datos;
  // a fracciones de la pagina (asi acompaña al zoom)
  const lineas = (datos.lineas || []).filter((l) => l.t && l.t.trim()).map((l) => ({
    t: l.t, x: l.x / datos.w, y: l.y / datos.h, w: l.w / datos.w, h: l.h / datos.h, a: l.a || 0,
  }));
  // orden de lectura: por renglones (de arriba hacia abajo) y, en cada renglon, de izquierda a derecha
  lineas.sort((p, q) => (p.y + p.h / 2) - (q.y + q.h / 2));
  const renglones = [];
  for (const l of lineas) {
    const cy = l.y + l.h / 2, r = renglones[renglones.length - 1];
    if (r && Math.abs(cy - r.cy) < 0.5 * Math.min(l.h, r.h)) { r.items.push(l); } else renglones.push({ cy, h: l.h, items: [l] });
  }
  return { lineas: renglones.flatMap((r) => r.items.sort((p, q) => p.x - q.x)) };
}

let ctxMedir = null;
function ponerCapaOcr(t, n) {
  const lineas = t.ocr?.[n];
  const pv = t.viewer.getPageView(n - 1);
  const capa = pv?.textLayer?.div;
  if (!Array.isArray(lineas) || !capa || capa.querySelector(".ocr")) return;
  const vp1 = pv.pdfPage.getViewport({ scale: 1 });
  ctxMedir ||= document.createElement("canvas").getContext("2d");
  ctxMedir.font = "100px sans-serif";
  const frag = document.createDocumentFragment();
  for (const l of lineas) {
    const s = document.createElement("span");
    s.className = "ocr";
    s.textContent = l.t;
    const alto = l.h * vp1.height;                    // en unidades de pagina
    const anchoTexto = ctxMedir.measureText(l.t).width / 100 * alto;
    s.style.cssText = `left:${(l.x * 100).toFixed(3)}%;top:${(l.y * 100).toFixed(3)}%;font-family:sans-serif;`
      + `--font-height:${alto.toFixed(2)}px;--scale-x:${anchoTexto > 0 ? ((l.w * vp1.width) / anchoTexto).toFixed(4) : 1};--rotate:${l.a.toFixed(1)}deg`;
    frag.append(s);
    const br = document.createElement("br");
    br.className = "ocr";
    frag.append(br);
  }
  capa.append(frag);
}

function resaltarSeleccion() {
  const t = sel?.t;
  if (!t?.uiManager || !sel) return;
  // el resaltado de pdf.js toma la seleccion del documento: se arma con las letras elegidas
  const L = sel.idx.letras, a = L[sel.s], b = L[sel.e - 1];
  document.body.classList.add("eligiendo");
  const r = document.createRange();
  r.setStart(a.nodo, a.i); r.setEnd(b.nodo, b.i + 1);
  const ds = document.getSelection();
  ds.removeAllRanges(); ds.addRange(r);
  limpiarSel();
  const P = pdfjsLib.AnnotationEditorParamsType;
  t.eventBus.dispatch("switchannotationeditorparams", { source: window, type: P.HIGHLIGHT_COLOR, value: COLORES_RES[prefs.colorRes]?.[1] });
  t.uiManager.highlightSelection("main_toolbar");
  setTimeout(() => {
    document.body.classList.remove("eligiendo");
    document.getSelection().removeAllRanges();
    if (modo === "marcar" && marcarTipo !== "texto") return;
    try { t.viewer.annotationEditorMode = { mode: pdfjsLib.AnnotationEditorType.NONE }; } catch (e) { /* nada */ }
  }, 250);
}

// ---------------------------------------------------------------- firmas y sellos
// cada una: {id, tipo: "trazo"|"imagen", w, h, trazos?, color, grosor, op}. Las imagenes van aparte (pdfol_img_<id>).
const MAX_GUARDADAS = 5;
const cacheImg = new Map();
function imgDe(f) {
  if (f.src) return f.src;
  if (!cacheImg.has(f.id)) { try { cacheImg.set(f.id, localStorage.getItem("pdfol_img_" + f.id) || ""); } catch (e) { cacheImg.set(f.id, ""); } }
  return cacheImg.get(f.id);
}
function listaDe(cat) { return cat === "sellos" ? prefs.sellos : prefs.firmas; }
function muestra(f) {
  if (f.tipo === "imagen") return `<img src="${imgDe(f)}" alt="" draggable="false" style="width:100%;height:100%;object-fit:contain;display:block;pointer-events:none">`;
  return svgFirma(f);
}
function svgFirma(f, color) {
  const paths = f.trazos.map((p) => `<path d="${caminoSuave(p)}"/>`).join("");
  return `<svg viewBox="0 0 ${f.w} ${f.h}" preserveAspectRatio="xMidYMid meet"><g fill="none" stroke="${color || f.color}" stroke-opacity="${f.op ?? 1}" stroke-width="${f.grosor}" stroke-linecap="round" stroke-linejoin="round">${paths}</g></svg>`;
}
function caminoSuave(p) {
  if (p.length < 4) return `M${p[0]} ${p[1]}l0.01 0`;
  let d = `M${p[0].toFixed(1)} ${p[1].toFixed(1)}`;
  for (let i = 2; i < p.length - 2; i += 2) {
    const mx = (p[i] + p[i + 2]) / 2, my = (p[i + 1] + p[i + 3]) / 2;
    d += `Q${p[i].toFixed(1)} ${p[i + 1].toFixed(1)} ${mx.toFixed(1)} ${my.toFixed(1)}`;
  }
  d += `L${p[p.length - 2].toFixed(1)} ${p[p.length - 1].toFixed(1)}`;
  return d;
}
function guardarEnLista(cat, f) {
  const l = listaDe(cat);
  if (l.length >= MAX_GUARDADAS) {
    aviso(`Ya tenés ${MAX_GUARDADAS} ${cat} guardados/as: borrá una para guardar otra. Esta se usa igual.`, 4000);
    return false;
  }
  if (f.tipo === "imagen") {
    try { localStorage.setItem("pdfol_img_" + f.id, f.src); } catch (e) { aviso("No hay espacio para guardar la imagen. Se usa igual."); return false; }
    cacheImg.set(f.id, f.src);
  }
  const g = { ...f };
  delete g.src;
  l.unshift(g);
  guardarPrefs();
  return true;
}
function borrarDeLista(cat, i) {
  const l = listaDe(cat);
  const [f] = l.splice(i, 1);
  if (f?.tipo === "imagen") { try { localStorage.removeItem("pdfol_img_" + f.id); } catch (e) { /* nada */ } cacheImg.delete(f.id); }
  guardarPrefs();
}

let catFirma = "firmas";
async function elegirFirma(cat = catFirma) {
  const t = tabAct();
  if (!t) return;
  catFirma = cat;
  const l = listaDe(cat);
  const html = `<div class="seg" id="seg-cat" style="margin-bottom:12px"><button data-c="firmas" class="${cat === "firmas" ? "sel" : ""}">Firmas</button><button data-c="sellos" class="${cat === "sellos" ? "sel" : ""}">Sellos</button></div>
    <p class="cuenta-g">${l.length ? `Tocá ${cat === "sellos" ? "un sello" : "una firma"} para ponerla. Guardadas: ${l.length} de ${MAX_GUARDADAS}.` : `Todavía no tenés ${cat} guardados/as.`}</p>
    <div class="firmas-guardadas">${l.map((f, i) => `<button class="firma-g" data-i="${i}">${muestra(f)}<span class="x" data-borrar="${i}">${svg(ICO.cerrar)}</span></button>`).join("")}</div>
    <div class="fila-herr"><button class="suave" id="g-dibujar">${svg(ICO.firma)}Dibujar</button><button class="suave" id="g-imagen">${svg('<rect x="3" y="5" width="18" height="14" rx="2"/><circle cx="9" cy="10" r="2"/><path d="m21 16-5-5-8 8"/>')}Desde imagen</button></div>`;
  const r = await dialogo({
    titulo: "Firmar", html, botones: [["no", "Cerrar"]],
    alAbrir: (d, fin) => {
      d.querySelectorAll("#seg-cat button").forEach((b) => { b.onclick = () => fin("cat:" + b.dataset.c); });
      d.querySelector("#g-dibujar").onclick = () => fin("dibujar");
      d.querySelector("#g-imagen").onclick = () => fin("imagen");
      d.querySelectorAll(".firma-g").forEach((b) => {
        b.onclick = (e) => {
          const borrar = e.target.closest("[data-borrar]");
          if (borrar) { borrarDeLista(cat, +borrar.dataset.borrar); fin("cat:" + cat); return; }
          fin("f" + b.dataset.i);
        };
      });
    },
  });
  if (!r || r === "no") return;
  if (r.startsWith("cat:")) return elegirFirma(r.slice(4));
  if (r === "dibujar") return dibujarFirmaNueva(cat);
  if (r === "imagen") return firmaDesdeImagen(cat);
  if (r[0] === "f") ponerFirma(t, l[+r.slice(1)], cat);
}

// selector de pluma, color y transparencia (lo usan el lapiz y el panel de firma)
function htmlPlumas(id) {
  return `<div class="plumas" id="${id}-plumas">${PLUMAS.map((p) => `<button data-p="${p.k}" aria-label="${p.t}"><svg viewBox="0 0 40 24" class="muestra-pluma"><path d="M4 16 Q 14 4 20 12 T 36 8" stroke-width="${Math.min(9, p.grosor)}" stroke-opacity="${p.op / 100}"/></svg><span>${p.t}</span></button>`).join("")}</div>
    <div class="colores" id="${id}-colores">${COLORES_TINTA.map(([n, c], i) => `<button class="color" data-i="${i}" style="background:${c}" aria-label="${n}"></button>`).join("")}</div>
    <div class="fila-herr deslizadores">
      <label class="grosor"><span>Grosor</span><input id="${id}-grosor" type="range" min="0.5" max="24" step="0.5"></label>
      <label class="grosor"><span>Opacidad</span><input id="${id}-op" type="range" min="10" max="100" step="5"><b id="${id}-opv"></b></label>
    </div>`;
}
// estado: {pluma, color, grosor, op}; al cambiar llama a alCambiar(estado)
function armarPlumas(raiz_, id, estado, alCambiar) {
  const q = (s) => raiz_.querySelector(s);
  const pintar = () => {
    raiz_.querySelectorAll(`#${id}-plumas button`).forEach((b) => b.classList.toggle("sel", b.dataset.p === estado.pluma));
    raiz_.querySelectorAll(`#${id}-colores .color`).forEach((b) => b.classList.toggle("sel", +b.dataset.i === estado.color));
    raiz_.querySelectorAll(`#${id}-plumas path`).forEach((p) => { p.style.stroke = COLORES_TINTA[estado.color][1]; });
    q(`#${id}-grosor`).value = estado.grosor;
    q(`#${id}-op`).value = estado.op;
    q(`#${id}-opv`).textContent = estado.op + " %";
  };
  raiz_.querySelectorAll(`#${id}-plumas button`).forEach((b) => {
    b.onclick = () => {
      const p = PLUMAS.find((x) => x.k === b.dataset.p);
      Object.assign(estado, { pluma: p.k, grosor: p.grosor, op: p.op });
      pintar(); alCambiar(estado);
    };
  });
  raiz_.querySelectorAll(`#${id}-colores .color`).forEach((b) => { b.onclick = () => { estado.color = +b.dataset.i; pintar(); alCambiar(estado); }; });
  q(`#${id}-grosor`).oninput = (e) => { estado.grosor = +e.target.value; pintar(); alCambiar(estado); };
  q(`#${id}-op`).oninput = (e) => { estado.op = +e.target.value; pintar(); alCambiar(estado); };
  pintar();
}

function dibujarFirmaNueva(cat = "firmas") {
  let trazos = [], guardarla = true;
  const est = { ...prefs.plumaFirma };
  const html = `<canvas class="pad-firma" id="pad"></canvas>${htmlPlumas("pf")}
    <div class="fila-herr" style="margin-top:6px">
      <label style="display:flex;gap:6px;align-items:center;font-size:13px;color:var(--texto2)"><input type="checkbox" id="guardarla" checked style="accent-color:var(--acento)">Guardar para la próxima</label>
      <button class="suave" id="pad-borrar" style="margin-left:auto">Borrar</button>
    </div>`;
  return dialogo({
    titulo: cat === "sellos" ? "Dibujá tu sello" : "Dibujá tu firma", html,
    botones: [["no", "Cancelar"], ["ok", "Usar", true]],
    alAbrir: (d) => {
      const cv = d.querySelector("#pad");
      const ctx = cv.getContext("2d");
      const dpr = window.devicePixelRatio || 1;
      const redibujar = () => {
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.clearRect(0, 0, cv.width, cv.height);
        ctx.globalAlpha = est.op / 100;
        ctx.strokeStyle = COLORES_TINTA[est.color][1]; ctx.lineWidth = est.grosor * 1.4; ctx.lineCap = "round"; ctx.lineJoin = "round";
        for (const p of trazos) ctx.stroke(new Path2D(caminoSuave(p)));
      };
      requestAnimationFrame(() => { cv.width = cv.clientWidth * dpr; cv.height = cv.clientHeight * dpr; redibujar(); });
      armarPlumas(d, "pf", est, () => { prefs.plumaFirma = { ...est }; guardarPrefs(); redibujar(); });
      let actual = null;
      const pos = (e) => { const r = cv.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
      cv.onpointerdown = (e) => { cv.setPointerCapture(e.pointerId); actual = [...pos(e)]; trazos.push(actual); redibujar(); };
      cv.onpointermove = (e) => {
        if (!actual) return;
        for (const ev of e.getCoalescedEvents ? e.getCoalescedEvents() : [e]) {
          const [x, y] = pos(ev);
          const n = actual.length;
          if (Math.hypot(x - actual[n - 2], y - actual[n - 1]) > 1.2) actual.push(x, y);
        }
        redibujar();
      };
      cv.onpointerup = cv.onpointercancel = () => { actual = null; };
      d.querySelector("#pad-borrar").onclick = () => { trazos = []; redibujar(); };
      d.querySelector("#guardarla").onchange = (e) => { guardarla = e.target.checked; };
    },
  }).then((r) => {
    if (r !== "ok") return;
    if (!trazos.length) { aviso("No dibujaste nada."); return; }
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const p of trazos) for (let i = 0; i < p.length; i += 2) {
      x0 = Math.min(x0, p[i]); x1 = Math.max(x1, p[i]); y0 = Math.min(y0, p[i + 1]); y1 = Math.max(y1, p[i + 1]);
    }
    const g = est.grosor * 1.4, m = g / 2 + 2;
    const f = {
      id: Date.now(), tipo: "trazo", w: Math.max(10, x1 - x0 + 2 * m), h: Math.max(10, y1 - y0 + 2 * m),
      color: COLORES_TINTA[est.color][1], grosor: g, op: est.op / 100,
      trazos: trazos.map((p) => p.map((v, i) => +(v - (i % 2 ? y0 : x0) + m).toFixed(1))),
    };
    if (guardarla) guardarEnLista(cat, f);
    const t = tabAct();
    if (t) ponerFirma(t, f, cat);
  });
}

// ---- firma o sello desde una foto o imagen: se quita el fondo claro (papel) y queda transparente
function cargarImagen(src) {
  return new Promise((res, rej) => { const i = new Image(); i.onload = () => res(i); i.onerror = rej; i.src = src; });
}
function elegirImagenArchivo() {
  return new Promise((res) => {
    const inp = $("imagen");
    inp.value = "";
    inp.onchange = () => res(inp.files[0] || null);
    inp.click();
  });
}
function recortarAlfa(cv) {
  const ctx = cv.getContext("2d", { willReadFrequently: true });
  const { width: w, height: h } = cv;
  const px = ctx.getImageData(0, 0, w, h).data;
  let x0 = w, y0 = h, x1 = -1, y1 = -1;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (px[(y * w + x) * 4 + 3] > 24) { if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
  }
  if (x1 < 0) return null;
  const m = 4;
  x0 = Math.max(0, x0 - m); y0 = Math.max(0, y0 - m); x1 = Math.min(w - 1, x1 + m); y1 = Math.min(h - 1, y1 + m);
  const out = document.createElement("canvas");
  out.width = x1 - x0 + 1; out.height = y1 - y0 + 1;
  out.getContext("2d").drawImage(cv, x0, y0, out.width, out.height, 0, 0, out.width, out.height);
  return out;
}
// sens: 0 (suave) .. 100 (fuerte)
function quitarFondo(img, quitar, sens) {
  const MAX = 1200;
  const k = Math.min(1, MAX / Math.max(img.naturalWidth, img.naturalHeight));
  const w = Math.max(1, Math.round(img.naturalWidth * k)), h = Math.max(1, Math.round(img.naturalHeight * k));
  const cv = document.createElement("canvas");
  cv.width = w; cv.height = h;
  const ctx = cv.getContext("2d", { willReadFrequently: true });
  ctx.drawImage(img, 0, 0, w, h);
  if (!quitar) return recortarAlfa(cv);
  const datos = ctx.getImageData(0, 0, w, h), px = datos.data;
  // 1) color del papel por bloques (lo mas claro de cada bloque), asi las sombras de la foto no molestan
  const B = Math.max(8, Math.round(Math.max(w, h) / 36));
  const bw = Math.ceil(w / B), bh = Math.ceil(h / B);
  let fondo = new Float32Array(bw * bh * 4); // r, g, b, luz
  const lum = (i) => px[i] * 0.3 + px[i + 1] * 0.59 + px[i + 2] * 0.11;
  for (let by = 0; by < bh; by++) for (let bx = 0; bx < bw; bx++) {
    const ls = [];
    for (let y = by * B; y < Math.min(h, by * B + B); y += 2) for (let x = bx * B; x < Math.min(w, bx * B + B); x += 2) {
      const i = (y * w + x) * 4;
      if (px[i + 3] > 128) ls.push(i);
    }
    const o = (by * bw + bx) * 4;
    if (!ls.length) { fondo.set([255, 255, 255, 255], o); continue; }
    ls.sort((a, b) => lum(a) - lum(b));
    const desde = Math.floor(ls.length * 0.8);
    let r = 0, g = 0, b = 0, n = 0;
    for (let j = desde; j < ls.length; j++) { r += px[ls[j]]; g += px[ls[j] + 1]; b += px[ls[j] + 2]; n++; }
    fondo.set([r / n, g / n, b / n, (r * 0.3 + g * 0.59 + b * 0.11) / n], o);
  }
  // 2) los bloques llenos de tinta toman el papel del vecino mas claro (dos pasadas)
  for (let pasada = 0; pasada < 2; pasada++) {
    const nuevo = fondo.slice();
    for (let by = 0; by < bh; by++) for (let bx = 0; bx < bw; bx++) {
      let mejor = (by * bw + bx) * 4;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const yy = by + dy, xx = bx + dx;
        if (yy < 0 || xx < 0 || yy >= bh || xx >= bw) continue;
        const o = (yy * bw + xx) * 4;
        if (fondo[o + 3] > fondo[mejor + 3] + 12) mejor = o;
      }
      nuevo.set(fondo.subarray(mejor, mejor + 4), (by * bw + bx) * 4);
    }
    fondo = nuevo;
  }
  // 3) cada pixel: cuanto mas oscuro que el papel, mas opaco; el color de la tinta se recupera
  const t0 = 12 + (100 - sens) * 0.45, t1 = t0 + 40;
  for (let y = 0; y < h; y++) {
    const fy = Math.min(bh - 1.001, Math.max(0, y / B - 0.5)), y0i = Math.floor(fy), ty = fy - y0i;
    for (let x = 0; x < w; x++) {
      const fx = Math.min(bw - 1.001, Math.max(0, x / B - 0.5)), x0i = Math.floor(fx), tx = fx - x0i;
      const i = (y * w + x) * 4;
      const o00 = (y0i * bw + x0i) * 4, o01 = o00 + 4, o10 = o00 + bw * 4, o11 = o10 + 4;
      const f = [0, 1, 2].map((c) => (fondo[o00 + c] * (1 - tx) + fondo[o01 + c] * tx) * (1 - ty) + (fondo[o10 + c] * (1 - tx) + fondo[o11 + c] * tx) * ty);
      const dist = Math.max(f[0] - px[i], f[1] - px[i + 1], f[2] - px[i + 2], 0);
      const a = Math.min(1, Math.max(0, (dist - t0) / (t1 - t0)));
      if (a <= 0) { px[i + 3] = 0; continue; }
      for (let c = 0; c < 3; c++) px[i + c] = Math.max(0, Math.min(255, Math.round(f[c] - (f[c] - px[i + c]) / Math.max(a, 0.35))));
      px[i + 3] = Math.round(px[i + 3] * a);
    }
  }
  ctx.putImageData(datos, 0, 0);
  return recortarAlfa(cv);
}

async function firmaDesdeImagen(cat = "firmas") {
  const archivo = await elegirImagenArchivo();
  if (!archivo) return;
  let img;
  try { img = await cargarImagen(URL.createObjectURL(archivo)); } catch (e) { aviso("No se pudo leer esa imagen."); return; }
  let quitar = true, sens = 50, guardarla = true, resultado = null;
  const html = `<div class="vista-img" id="vista-img"></div>
    <label class="fila-chk"><input type="checkbox" id="quitar" checked> Quitar el fondo claro (queda transparente)</label>
    <label class="grosor" id="fila-sens"><span>Intensidad</span><input id="sens" type="range" min="0" max="100" value="50"></label>
    <label class="fila-chk"><input type="checkbox" id="guardarla2" checked> Guardar para la próxima</label>`;
  const r = await dialogo({
    titulo: cat === "sellos" ? "Sello desde imagen" : "Firma desde imagen", html,
    botones: [["no", "Cancelar"], ["ok", "Usar", true]],
    alAbrir: (d) => {
      const vista = d.querySelector("#vista-img");
      const actualizar = () => {
        resultado = quitarFondo(img, quitar, sens);
        vista.innerHTML = "";
        if (resultado) { resultado.style.maxWidth = "100%"; resultado.style.maxHeight = "220px"; vista.append(resultado); }
        else vista.textContent = "No quedó nada: bajá la intensidad.";
        d.querySelector("#fila-sens").hidden = !quitar;
      };
      let tt = 0;
      d.querySelector("#quitar").onchange = (e) => { quitar = e.target.checked; actualizar(); };
      d.querySelector("#sens").oninput = (e) => { sens = +e.target.value; clearTimeout(tt); tt = setTimeout(actualizar, 120); };
      d.querySelector("#guardarla2").onchange = (e) => { guardarla = e.target.checked; };
      setTimeout(actualizar, 30);
    },
  });
  URL.revokeObjectURL(img.src);
  if (r !== "ok" || !resultado) return;
  const f = { id: Date.now(), tipo: "imagen", w: resultado.width, h: resultado.height, src: resultado.toDataURL("image/webp", 0.92) };
  if (!f.src.startsWith("data:image/webp")) f.src = resultado.toDataURL("image/png");
  if (guardarla) guardarEnLista(cat, f);
  const t = tabAct();
  if (t) ponerFirma(t, f, cat);
}

// firma sobre la pagina: posicion en fracciones de la pagina (asi acompaña al zoom)
function ponerFirma(t, f, cat = "firmas") {
  const n = t.viewer.currentPageNumber;
  const pv = t.viewer.getPageView(n - 1);
  if (!pv) return;
  // centrada en lo que se ve de la pagina actual
  const pr = pv.div.getBoundingClientRect(), cr = t.cont.getBoundingClientRect();
  const visY0 = Math.max(pr.top, cr.top), visY1 = Math.min(pr.bottom, cr.bottom);
  const cy = ((visY0 + visY1) / 2 - pr.top) / pr.height;
  let fw = cat === "sellos" ? 0.3 : 0.38;
  if (fw * (f.h / f.w) * (pr.width / pr.height) > 0.35) fw = 0.35 / ((f.h / f.w) * (pr.width / pr.height));
  const fh = fw * (f.h / f.w) * (pr.width / pr.height);
  const firma = { pag: n, x: 0.5 - fw / 2, y: Math.min(1 - fh, Math.max(0, cy - fh / 2)), w: fw, f: { ...f } };
  t.firmas.push(firma);
  marcarModificado(t, true);
  dibujarFirmas(t);
  editarFirma(t, firma);
}

function dibujarFirmas(t) {
  const capa = t.cont.querySelector(".capa-firmas");
  capa.innerHTML = "";
  for (const fi of t.firmas) {
    const el = document.createElement("div");
    el.className = "firma-en-pag" + (fi === t.firmaEdit ? " edit" : "");
    el.innerHTML = muestra(fi.f) + '<div class="tirador"></div>';
    fi.el = el;
    capa.append(el);
    arrastrarFirma(t, fi, el);
  }
  ubicarFirmas(t);
}
function ubicarFirmas(t) {
  if (!t.firmas.length) return;
  cancelAnimationFrame(t.rafFirmas);
  t.rafFirmas = requestAnimationFrame(() => {
    for (const fi of t.firmas) {
      const pv = t.viewer.getPageView(fi.pag - 1);
      if (!pv || !fi.el) continue;
      const d = pv.div;
      const W = d.offsetWidth, H = d.offsetHeight;
      const w = fi.w * W, h = w * fi.f.h / fi.f.w;
      Object.assign(fi.el.style, {
        left: d.offsetLeft + fi.x * W + "px", top: d.offsetTop + fi.y * H + "px", width: w + "px", height: h + "px",
      });
    }
  });
}
function editarFirma(t, fi) {
  t.firmaEdit = fi;
  for (const x of t.firmas) x.el?.classList.toggle("edit", x === fi);
  if (fi) {
    if (modo === "marcar") salirDeModo();
    modo = "firma";
    $("herr-firma").hidden = false;
  } else if (modo === "firma") {
    modo = "ver"; $("herr-firma").hidden = true;
  }
  dibujarAcciones();
}
function arrastrarFirma(t, fi, el) {
  let ini = null;
  el.addEventListener("pointerdown", (e) => {
    e.preventDefault(); e.stopPropagation();
    if (t.firmaEdit !== fi) { editarFirma(t, fi); return; }
    el.setPointerCapture(e.pointerId);
    const pv = t.viewer.getPageView(fi.pag - 1);
    ini = { x: e.clientX, y: e.clientY, fx: fi.x, fy: fi.y, fw: fi.w, W: pv.div.offsetWidth, H: pv.div.offsetHeight,
      tam: e.target.classList.contains("tirador") };
  });
  el.addEventListener("pointermove", (e) => {
    if (!ini) return;
    const dx = (e.clientX - ini.x) / ini.W, dy = (e.clientY - ini.y) / ini.H;
    if (ini.tam) {
      fi.w = Math.min(0.95, Math.max(0.06, ini.fw + dx));
    } else {
      const hFrac = fi.w * (fi.f.h / fi.f.w) * (ini.W / ini.H);
      fi.x = Math.min(1 - fi.w, Math.max(0, ini.fx + dx));
      fi.y = Math.min(1 - hFrac, Math.max(0, ini.fy + dy));
    }
    ubicarFirmas(t);
  });
  const fin = () => { ini = null; };
  el.addEventListener("pointerup", fin);
  el.addEventListener("pointercancel", fin);
}
$("f-listo").onclick = () => { const t = tabAct(); if (t) editarFirma(t, null); };
$("f-quitar").onclick = () => {
  const t = tabAct();
  if (!t?.firmaEdit) return;
  t.firmas.splice(t.firmas.indexOf(t.firmaEdit), 1);
  t.firmaEdit = null;
  dibujarFirmas(t);
  editarFirma(t, null);
  if (!t.firmas.length && !t.editado) marcarModificado(t, false);
};
$("f-otra").onclick = () => { const t = tabAct(); if (t) { editarFirma(t, null); elegirFirma(); } };

async function pngDe(src) {
  const img = await cargarImagen(src);
  const cv = document.createElement("canvas");
  cv.width = img.naturalWidth; cv.height = img.naturalHeight;
  cv.getContext("2d").drawImage(img, 0, 0);
  const blob = await new Promise((r) => cv.toBlob(r, "image/png"));
  return new Uint8Array(await blob.arrayBuffer());
}
// estampa firmas y sellos en el PDF (los dibujados quedan vectoriales, nitidos a cualquier zoom)
async function estamparFirmas(t, datos) {
  const L = window.PDFLib;
  const doc = await L.PDFDocument.load(datos, { updateMetadata: false });
  for (const fi of t.firmas) {
    const pag = await t.pdf.getPage(fi.pag);
    const vp = pag.getViewport({ scale: 1 });
    const x0 = fi.x * vp.width, y0 = fi.y * vp.height;
    const w = fi.w * vp.width, h = w * fi.f.h / fi.f.w;
    const TL = vp.convertToPdfPoint(x0, y0), TR = vp.convertToPdfPoint(x0 + w, y0), BL = vp.convertToPdfPoint(x0, y0 + h);
    const hoja = doc.getPage(fi.pag - 1);
    if (fi.f.tipo === "imagen") { // imagen con fondo transparente: se dibuja en su caja
      const png = await pngDe(imgDe(fi.f));
      const im = await doc.embedPng(png);
      const nombre = hoja.node.newXObject("Firma", im.ref);
      hoja.pushOperators(L.pushGraphicsState(),
        L.concatTransformationMatrix(TR[0] - TL[0], TR[1] - TL[1], -(BL[0] - TL[0]), -(BL[1] - TL[1]), BL[0], BL[1]),
        L.drawObject(nombre), L.popGraphicsState());
      continue;
    }
    const s = w / fi.f.w; // unidades de la firma -> puntos de pagina
    const a = (TR[0] - TL[0]) / fi.f.w, b = (TR[1] - TL[1]) / fi.f.w, c = (BL[0] - TL[0]) / fi.f.h, d = (BL[1] - TL[1]) / fi.f.h;
    const hex = fi.f.color.replace("#", "");
    const [r, g, bl] = [0, 2, 4].map((i) => parseInt(hex.slice(i, i + 2), 16) / 255);
    const ops = [L.pushGraphicsState(), L.concatTransformationMatrix(a, b, c, d, TL[0], TL[1]),
      L.setLineWidth(Math.max(fi.f.grosor, 0.7 / s)), L.setLineCap(L.LineCapStyle.Round), L.setLineJoin(L.LineJoinStyle.Round),
      L.setStrokingRgbColor(r, g, bl)];
    if ((fi.f.op ?? 1) < 1) { // transparencia de la pluma
      const gs = doc.context.register(doc.context.obj({ Type: "ExtGState", CA: fi.f.op, ca: fi.f.op }));
      ops.splice(1, 0, L.setGraphicsState(hoja.node.newExtGState("GS", gs)));
    }
    for (const p of fi.f.trazos) {
      ops.push(L.moveTo(p[0], p[1]));
      if (p.length < 4) { ops.push(L.lineTo(p[0] + 0.01, p[1])); continue; }
      let px = p[0], py = p[1];
      for (let i = 2; i < p.length - 2; i += 2) {
        const qx = p[i], qy = p[i + 1], ex = (p[i] + p[i + 2]) / 2, ey = (p[i + 1] + p[i + 3]) / 2;
        // curva cuadratica -> cubica
        ops.push(L.appendBezierCurve(px + 2 / 3 * (qx - px), py + 2 / 3 * (qy - py), ex + 2 / 3 * (qx - ex), ey + 2 / 3 * (qy - ey), ex, ey));
        px = ex; py = ey;
      }
      ops.push(L.lineTo(p[p.length - 2], p[p.length - 1]));
    }
    ops.push(L.stroke(), L.popGraphicsState());
    hoja.pushOperators(...ops);
  }
  return await doc.save({ useObjectStreams: true });
}

// ---------------------------------------------------------------- guardar y compartir
async function bytesFinales(t) {
  if (modo === "marcar") salirDeModo();
  let datos = t.editado ? await t.pdf.saveDocument() : await t.pdf.getData();
  if (t.firmas.length) {
    try {
      datos = await estamparFirmas(t, datos);
    } catch (e) {
      console.error(e);
      throw new Error(/encrypt/i.test(String(e)) ? "Este PDF está protegido y no se puede firmar." : "No se pudo poner la firma en el PDF.");
    }
  }
  return datos;
}

const escrituras = new Map();
function a64(u8) {
  let s = "";
  for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000));
  return btoa(s);
}
// manda los bytes a Android por partes y espera el resultado
function escribirNativo(datos, modoEsc, t, nombre) {
  return new Promise((resolve) => {
    const token = AN.nuevaEscritura();
    const PARTE = 3 * 262144;
    for (let i = 0; i < datos.length; i += PARTE) {
      if (!AN.escribirParte(token, a64(datos.subarray(i, i + PARTE)))) { resolve({ ok: false, msg: "No hay espacio para guardar." }); return; }
    }
    escrituras.set(token, resolve);
    AN.terminarEscritura(token, modoEsc, t.idNativo || "", nombre);
  });
}
function nombreCopia(n) { return n.replace(/(\.pdf)?$/i, " (PdFOL).pdf"); }

async function guardar(como) {
  const t = tabAct();
  if (!t) return false;
  if (!t.modificado && como !== "copia") { aviso("No hay cambios para guardar."); return true; }
  aviso("Guardando…", 20000);
  let datos;
  try { datos = await bytesFinales(t); } catch (e) { aviso(e.message || "No se pudo guardar."); return false; }
  const pag = t.viewer.currentPageNumber, esc = t.viewer.currentScaleValue;
  if (!AN) { // navegador (pruebas): se descarga
    const a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob([datos], { type: "application/pdf" }));
    a.download = como === "copia" ? nombreCopia(t.nombre) : t.nombre;
    a.click();
    await abrirDoc({ nombre: t.nombre, datos: datos.slice(), pagina: pag, escala: esc }, { reemplazar: t });
    aviso("PDF guardado.");
    return true;
  }
  let modoEsc = como === "copia" || !t.escribible || !t.idNativo ? "copia" : "original";
  let r = await escribirNativo(datos, modoEsc, t, modoEsc === "copia" ? nombreCopia(t.nombre) : t.nombre);
  if (!r.ok && r.msg === "sinpermiso") {
    $("toast").hidden = true;
    const q = await dialogo({
      titulo: "No se puede guardar encima",
      texto: "La app desde donde abriste este PDF no deja modificarlo. Guardá una copia con las marcas y firmas.",
      botones: [["no", "Cancelar"], ["copia", "Guardar copia", true]],
    });
    if (q !== "copia") return false;
    aviso("Guardando…", 20000);
    t.escribible = false;
    r = await escribirNativo(datos, "copia", t, nombreCopia(t.nombre));
  }
  if (!r.ok) { aviso(r.msg === "cancelado" ? "No se guardó." : (r.msg || "No se pudo guardar.")); return false; }
  const ex = r.extra || {};
  await abrirDoc({
    nombre: ex.nombre || t.nombre, idNativo: ex.id || t.idNativo, uri: ex.uri || t.uri, persistente: ex.persistente,
    escribible: ex.id ? true : t.escribible, pagina: pag, escala: esc,
  }, { reemplazar: t });
  aviso(ex.nombre && ex.nombre !== t.nombre ? `Guardado como «${ex.nombre}».` : "PDF guardado.");
  return true;
}

async function compartir() {
  const t = tabAct();
  if (!t) return;
  let datos;
  try { datos = t.modificado ? await bytesFinales(t) : await t.pdf.getData(); } catch (e) { aviso(e.message); return; }
  if (!AN) {
    const file = new File([datos], t.nombre, { type: "application/pdf" });
    if (navigator.canShare?.({ files: [file] })) navigator.share({ files: [file] }).catch(() => {});
    else aviso("Compartir funciona en la app de Android.");
    return;
  }
  const r = await escribirNativo(datos, "compartir", t, t.nombre);
  if (!r.ok) aviso(r.msg || "No se pudo compartir.");
}

// ---------------------------------------------------------------- recientes (solo los que Android deja volver a abrir)
function anotarReciente(nombre, uri) {
  prefs.recientes = [{ nombre, uri, fecha: Date.now() }, ...prefs.recientes.filter((r) => r.uri !== uri)].slice(0, 8);
  guardarPrefs();
}
function dibujarRecientes() {
  const c = $("recientes");
  c.innerHTML = "";
  if (!AN || !prefs.recientes.length) return;
  c.insertAdjacentHTML("beforeend", "<h2>Recientes</h2>");
  for (const r of prefs.recientes) {
    const b = document.createElement("button");
    b.className = "reciente";
    b.innerHTML = `${svg(ICO.doc, 'class="ic-doc"')}<div><div class="r-nom"></div><div class="r-fecha"></div></div>`;
    b.querySelector(".r-nom").textContent = r.nombre;
    b.querySelector(".r-fecha").textContent = new Date(r.fecha).toLocaleDateString("es", { day: "numeric", month: "short", year: "numeric" });
    b.onclick = async () => {
      let d = null;
      try { d = JSON.parse(AN.reabrir(r.uri) || "null"); } catch (e) { /* nada */ }
      if (!d) {
        aviso("Ese archivo ya no está disponible.");
        prefs.recientes = prefs.recientes.filter((x) => x !== r); guardarPrefs(); dibujarRecientes();
        return;
      }
      await abrirDoc({ nombre: d.nombre, idNativo: d.id, uri: r.uri, persistente: true, escribible: d.escribible });
    };
    c.append(b);
  }
}

// ---------------------------------------------------------------- apariencia, novedades, acerca de, actualizaciones
function dialogoApariencia() {
  const op = (grupo, val, txt, muestra) => `<button class="opcion${prefs[grupo] === val ? " sel" : ""}" data-g="${grupo}" data-v="${val}">${muestra ? `<span class="muestra" style="background:${muestra}"></span>` : ""}<span>${txt}</span></button>`;
  dialogo({
    titulo: "Apariencia",
    html: `<p>Color del tema</p><div class="opciones">${op("tema", "azul", "Azul gris", "#4C6F9F")}${op("tema", "verde", "Verde gris", "#9FB0A6")}</div>
      <p style="margin-top:14px">Modo</p><div class="opciones">${op("modo", "auto", "Automático (como el teléfono)")}${op("modo", "claro", "Claro")}${op("modo", "oscuro", "Oscuro")}</div>`,
    botones: [["ok", "Listo", true]],
    alAbrir: (d) => {
      d.querySelectorAll(".opcion").forEach((b) => {
        b.onclick = () => {
          prefs[b.dataset.g] = b.dataset.v; guardarPrefs(); aplicarTema();
          d.querySelectorAll(`.opcion[data-g="${b.dataset.g}"]`).forEach((x) => x.classList.toggle("sel", x === b));
        };
      });
    },
  });
}
function htmlCambios(lista) {
  return lista.map(([v, items]) => `<div class="ver-tit">v${v}</div><ul>${items.map((x) => `<li>${x}</li>`).join("")}</ul>`).join("");
}
function verNovedades() {
  dialogo({ titulo: "Novedades de PdFOL", html: htmlCambios(CAMBIOS), botones: [["ok", "Listo", true]] });
}
function acercaDe() {
  dialogo({
    titulo: `PdFOL v${VERSION} para Android`,
    html: `<p>Visor de PDF: buscar, marcar y firmar.<br><b>by Meneses999</b></p>
      <p>Las firmas quedan dibujadas en el PDF (firma manuscrita, no certificado digital).</p>
      <p style="font-size:12px">Usa pdf.js (Mozilla, licencia Apache 2.0) y pdf-lib (licencia MIT).</p>${htmlCambios(CAMBIOS.slice(0, 1))}`,
    botones: [["ok", "Cerrar", true]],
  });
}
function compararVersion(a, b) {
  const x = a.split(".").map(Number), y = b.split(".").map(Number);
  for (let i = 0; i < Math.max(x.length, y.length); i++) { if ((x[i] || 0) !== (y[i] || 0)) return (x[i] || 0) - (y[i] || 0); }
  return 0;
}
async function buscarActualizacion(manual) {
  if (!manual && Date.now() - prefs.ultimaRevision < 12 * 3600e3) { marcarNueva(); return; }
  if (manual) aviso("Buscando actualizaciones…", 8000);
  try {
    const r = await fetch(`https://api.github.com/repos/${REPO}/releases?per_page=30`, { headers: { Accept: "application/vnd.github+json" } });
    const lista = await r.json();
    prefs.ultimaRevision = Date.now();
    let mejor = null;
    for (const rel of lista) {
      const m = /^android-v(\d+(?:\.\d+)*)$/.exec(rel.tag_name || "");
      if (!m || rel.draft) continue;
      let abi = "";
      try { abi = AN?.abi ? AN.abi() : ""; } catch (e) { /* nada */ }
      const apks = (rel.assets || []).filter((a) => a.name.endsWith(".apk"));
      const de32 = apks.find((a) => /32bits/i.test(a.name)), de64 = apks.find((a) => !/32bits/i.test(a.name));
      const apk = abi && !abi.startsWith("arm64") && de32 ? de32 : de64 || apks[0];
      if (apk && compararVersion(m[1], VERSION) > 0 && (!mejor || compararVersion(m[1], mejor.version) > 0)) {
        mejor = { version: m[1], url: apk.browser_download_url, notas: rel.body || "" };
      }
    }
    prefs.nuevaVersion = mejor;
    guardarPrefs();
    marcarNueva();
    if (manual) {
      $("toast").hidden = true;
      if (mejor) ofrecerActualizacion(); else dialogo({ titulo: "PdFOL está al día", texto: `Tenés la última versión (v${VERSION}).` });
    }
  } catch (e) {
    if (manual) aviso("Sin conexión: no se pudo revisar.");
  }
}
function marcarNueva() {
  const n = prefs.nuevaVersion;
  if (n && compararVersion(n.version, VERSION) <= 0) prefs.nuevaVersion = null;
  document.querySelector(".logo .punto").hidden = !prefs.nuevaVersion;
}
async function ofrecerActualizacion() {
  const n = prefs.nuevaVersion;
  if (!n) return;
  const notas = n.notas.replace(/\*\*/g, "").split("\n").filter((l) => /^\s*[-*]/.test(l)).map((l) => l.replace(/^\s*[-*]\s*/, ""));
  const r = await dialogo({
    titulo: `Hay una versión nueva: v${n.version}`,
    html: (notas.length ? `<ul>${notas.map((x) => `<li></li>`).join("")}</ul>` : "") + "<p>Se descarga el instalador; abrilo para actualizar. Tus firmas y preferencias se mantienen.</p>",
    botones: [["no", "Después"], ["si", "Descargar", true]],
    alAbrir: (d) => d.querySelectorAll("li").forEach((li, i) => { li.textContent = notas[i]; }),
  });
  if (r === "si") { if (AN) AN.abrirUrl(n.url); else window.open(n.url); }
}

// ---------------------------------------------------------------- boton Atras de Android
window.pdfolAtras = function () {
  if (dialogoAbierto) { dialogoAbierto.alVelo ? dialogoAbierto.alVelo() : cerrarCapas(); return true; }
  if (sel) { limpiarSel(); return true; }
  if (!$("miniaturas").hidden && !esAncho()) { alternarMinis(); return true; }
  if (!$("busqueda").hidden) { cerrarBusqueda(); return true; }
  if (modo !== "ver") { salirDeModo(); return true; }
  if (pest.length) { cerrarPestana(act); return true; }
  return false;
};
document.addEventListener("keydown", (e) => {
  if ((e.ctrlKey || e.metaKey) && (e.key === "f" || e.key === "b")) { e.preventDefault(); if ($("busqueda").hidden) alternarBusqueda(); else $("q").focus(); }
  if ((e.ctrlKey || e.metaKey) && e.key === "s") { e.preventDefault(); guardar(); }
  if ((e.ctrlKey || e.metaKey) && e.key === "o") { e.preventDefault(); elegirArchivo(); }
});

// ---------------------------------------------------------------- arranque
window.addEventListener("resize", () => {
  dibujarAcciones();
  const t = tabAct();
  if (t) { $("zoom-fab").hidden = !esAncho(); ubicarFirmas(t); }
  // al girar el telefono o cambiar el tamaño: «Ajustar al ancho» se vuelve a ajustar
  clearTimeout(window._tAjuste);
  window._tAjuste = setTimeout(() => {
    for (const x of pest) {
      const v = x.viewer.currentScaleValue;
      if (v && isNaN(+v)) x.viewer.currentScaleValue = v;
    }
  }, 150);
  if (esAncho()) $("velo-minis").hidden = true;
});
$("ver").textContent = "v" + VERSION;
$("ver2").textContent = "v" + VERSION;
aplicarTema();
dibujarAcciones();
dibujarRecientes();
marcarNueva();
(async () => {
  try { await cargarLibs(); } catch (e) { aviso("No se pudo cargar el visor. Actualizá «Android System WebView» desde Play Store.", 15000); console.error(e); }
  if (AN) { await window.pdfolNativo.nuevos(); try { AN.listo(); } catch (e) { /* nada */ } }
  if (esAncho() && prefs.minis && tabAct()) alternarMinis();
  setTimeout(() => buscarActualizacion(false), 4000);
})();
// para las pruebas automaticas
window._pdfol = { pest, abrirDoc, guardar, bytesFinales, ponerFirma, prefs, entrarMarcar, ponerTipoMarca, alternarBusqueda, buscar, salirDeModo };
