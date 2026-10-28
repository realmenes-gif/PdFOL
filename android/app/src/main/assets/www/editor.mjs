// PdFOL · cambiar texto existente del PDF con MuPDF (WASM, se carga solo al usarlo).
// Coordenadas: puntos de la pagina vista (origen arriba a la izquierda, ya girada) = las de pdf.js a escala 1.
import * as mupdf from "./lib/mupdf/mupdf.js";

const docs = new Map(); // clave -> mupdf.PDFDocument (para leer el texto)

export function abrir(clave, bytes) {
  let d = docs.get(clave);
  if (!d) { d = mupdf.PDFDocument.openDocument(bytes, "application/pdf").asPDF(); docs.set(clave, d); }
  return d;
}
export function cerrar(clave) { const d = docs.get(clave); if (d) { try { d.destroy(); } catch (e) { /* nada */ } docs.delete(clave); } }

const masComun = (arr) => {
  const m = new Map(); let mejor = arr[0], n = 0;
  for (const v of arr) { const k = JSON.stringify(v); const c = (m.get(k) || 0) + 1; m.set(k, c); if (c > n) { n = c; mejor = v; } }
  return mejor;
};
function familia(nombre, font) {
  const s = (nombre || "").toLowerCase();
  const mono = /courier|mono|consol/.test(s) || font?.isMono?.();
  const serif = !mono && (/times|serif|roman|georgia|garamond|cambria|book/.test(s.replace("sans", "")) || (font?.isSerif?.() && !/sans|arial|helv|calibri|verdana/.test(s)));
  const negrita = /bold|black|heavy|semibold|demi/.test(s) || !!font?.isBold?.();
  const cursiva = /italic|oblique/.test(s) || !!font?.isItalic?.();
  return { fam: mono ? "Courier" : serif ? "Times" : "Helvetica", negrita, cursiva };
}
function aRgb(c) {
  if (!c) return [0, 0, 0];
  if (c.length === 1) return [c[0], c[0], c[0]];
  if (c.length === 4) return [(1 - c[0]) * (1 - c[3]), (1 - c[1]) * (1 - c[3]), (1 - c[2]) * (1 - c[3])];
  return c.slice(0, 3);
}

// bloques de texto (parrafos) de una pagina, con sus lineas
export function bloques(clave, nPag) {
  const d = docs.get(clave);
  const pag = d.loadPage(nPag - 1);
  const st = pag.toStructuredText("preserve-whitespace");
  const res = [];
  let b = null, l = null;
  st.walk({
    beginTextBlock(bbox) { b = { bbox, lineas: [] }; },
    endTextBlock() { if (b && b.lineas.length) res.push(b); b = null; },
    beginLine(bbox, wmode, dir) { l = { bbox, dir, txt: "", base: null, x0: null, info: [] }; },
    endLine() { if (b && l && l.txt.trim()) b.lineas.push(l); l = null; },
    onChar(c, origin, font, size, quad, color) {
      if (!l) return;
      if (l.base === null) { l.base = origin[1]; l.x0 = origin[0]; }
      l.txt += c;
      if (c.trim()) l.info.push({ nombre: font.getName(), font, size: Math.round(size * 10) / 10, color: aRgb(color) });
    },
  });
  st.destroy?.();
  pag.destroy?.();
  return res.map((blq) => {
    const inf = blq.lineas.flatMap((x) => x.info);
    const f0 = masComun(inf.map((i) => i.nombre));
    const fi = inf.find((i) => i.nombre === f0);
    const horizontal = blq.lineas.every((x) => Math.abs(x.dir[1]) < 0.01 && x.dir[0] > 0);
    const lineas = blq.lineas.map((x) => {
      const fl = familia(masComun(x.info.map((i) => i.nombre)), x.info[0]?.font);
      return { bbox: x.bbox, txt: x.txt.replace(/\s+$/, ""), base: x.base, x0: x.x0,
        tam: masComun(x.info.map((i) => i.size)), color: masComun(x.info.map((i) => i.color)), ...fl };
    });
    // une las lineas que siguen el mismo renglon del parrafo (las cortadas por el ancho)
    const ancho = blq.bbox[2] - blq.bbox[0];
    let txt = "";
    lineas.forEach((x, i) => {
      txt += x.txt.trim();
      if (i < lineas.length - 1) txt += (x.bbox[2] >= blq.bbox[0] + ancho * 0.8 && !/[.:;]$/.test(x.txt.trim())) ? " " : "\n";
    });
    const dir = blq.lineas[0].dir;
    let inter = 0; // distancia entre renglones, medida perpendicular a la escritura
    for (let i = 1; i < lineas.length; i++) inter += (lineas[i].x0 - lineas[i - 1].x0) * -dir[1] + (lineas[i].base - lineas[i - 1].base) * dir[0];
    const tam = masComun(inf.map((i) => i.size));
    return {
      bbox: blq.bbox, txt, lineas, horizontal, dir,
      tam, color: masComun(inf.map((i) => i.color)), ...familia(f0, fi?.font),
      inter: lineas.length > 1 ? inter / (lineas.length - 1) : tam * 1.2,
    };
  });
}

// el bloque (o la linea) bajo un punto
export function bajoPunto(clave, nPag, x, y) {
  const bs = bloques(clave, nPag);
  const dentro = (r, m) => x >= r[0] - m && x <= r[2] + m && y >= r[1] - m && y <= r[3] + m;
  for (const m of [0, 4, 10]) {
    for (const b of bs) {
      if (!dentro(b.bbox, m)) continue;
      const li = b.lineas.findIndex((l) => dentro(l.bbox, m + 2));
      return { bloque: b, linea: li >= 0 ? li : 0 };
    }
  }
  return null;
}

// ---- escribir el texto nuevo
const BASE14 = {
  Helvetica: ["Helvetica", "Helvetica-Bold", "Helvetica-Oblique", "Helvetica-BoldOblique"],
  Times: ["Times-Roman", "Times-Bold", "Times-Italic", "Times-BoldItalic"],
  Courier: ["Courier", "Courier-Bold", "Courier-Oblique", "Courier-BoldOblique"],
};
const nombreBase14 = (e) => BASE14[e.fam][(e.negrita ? 1 : 0) + (e.cursiva ? 2 : 0)];

function partir(texto, font, tam, ancho) {
  const medir = (s) => { let w = 0; for (const ch of s) w += font.advanceGlyph(font.encodeCharacter(ch.codePointAt(0)), 0); return w * tam; };
  const out = [];
  for (const parr of texto.split("\n")) {
    const pal = parr.split(/ +/);
    let lin = "";
    for (const p of pal) {
      const prueba = lin ? lin + " " + p : p;
      if (lin && medir(prueba) > ancho) { out.push(lin); lin = p; } else lin = prueba;
    }
    out.push(lin);
  }
  return out;
}
function hexWinAnsi(s) {
  const cp1252 = { 0x20AC: 0x80, 0x201A: 0x82, 0x201E: 0x84, 0x2026: 0x85, 0x2018: 0x91, 0x2019: 0x92, 0x201C: 0x93, 0x201D: 0x94, 0x2022: 0x95, 0x2013: 0x96, 0x2014: 0x97 };
  let h = "";
  for (const ch of s) {
    const u = ch.codePointAt(0);
    const c = u < 256 ? u : cp1252[u] ?? 0x3F;
    h += c.toString(16).padStart(2, "0");
  }
  return h;
}
const num = (v) => (Math.round(v * 1000) / 1000).toString();

// cambios: [{pag, rect:[x0,y0,x1,y1], txt, tam, color:[r,g,b], fam, negrita, cursiva, base, x0, inter, dir}]
export function aplicar(bytes, cambios) {
  const d = mupdf.PDFDocument.openDocument(bytes, "application/pdf").asPDF();
  const porPag = new Map();
  for (const c of cambios) { if (!porPag.has(c.pag)) porPag.set(c.pag, []); porPag.get(c.pag).push(c); }
  const fuentes = new Map();
  const fuente = (nombre) => {
    if (!fuentes.has(nombre)) { const f = new mupdf.Font(nombre); fuentes.set(nombre, { f, ref: d.addSimpleFont(f, "Latin") }); }
    return fuentes.get(nombre);
  };
  for (const [nPag, lista] of porPag) {
    const pag = d.loadPage(nPag - 1);
    // 1) borra el texto viejo (deja dibujos e imagenes)
    for (const c of lista) {
      const a = pag.createAnnotation("Redact");
      a.setRect(c.rect);
      a.update();
    }
    pag.applyRedactions(false, mupdf.PDFPage.REDACT_IMAGE_NONE, mupdf.PDFPage.REDACT_LINE_ART_NONE, mupdf.PDFPage.REDACT_TEXT_REMOVE);
    // 2) escribe el nuevo en su lugar
    const inv = mupdf.Matrix.invert(pag.getTransform());
    const obj = pag.getObject();
    let recursos = obj.getInheritable("Resources");
    if (recursos.isNull()) { recursos = d.newDictionary(); }
    else if (recursos.isIndirect() || obj.get("Resources").isNull()) recursos = recursos.resolve(); // se copia abajo
    const propios = d.newDictionary();
    recursos.forEach((v, k) => propios.put(k, v));
    let dicFuentes = d.newDictionary();
    const fViejas = propios.get("Font");
    if (!fViejas.isNull()) fViejas.forEach((v, k) => dicFuentes.put(k, v));
    let ops = "";
    for (const [i, c] of lista.entries()) {
      if (!c.txt.trim()) continue;
      const nb = nombreBase14(c);
      const { f, ref } = fuente(nb);
      const clave = "PdfolF" + Object.keys(BASE14).flatMap((k) => BASE14[k]).indexOf(nb);
      dicFuentes.put(clave, ref);
      const dir = c.dir || [1, 0];
      const vert = Math.abs(dir[1]) > Math.abs(dir[0]);
      const ancho = c.ajustar === false ? Infinity : Math.max(vert ? c.rect[3] - c.rect[1] : c.rect[2] - c.rect[0], c.tam * 2) + 1;
      const lineas = partir(c.txt, f, c.tam, ancho);
      const inter = c.inter || c.tam * 1.2;
      const [r, g, b] = c.color || [0, 0, 0];
      ops += `q ${num(r)} ${num(g)} ${num(b)} rg BT\n`;
      lineas.forEach((ln, j) => {
        // cada renglon baja en perpendicular a la direccion de escritura
        const x = (c.x0 ?? c.rect[0]) - dir[1] * j * inter, y = (c.base ?? c.rect[1] + c.tam) + dir[0] * j * inter;
        // texto (y hacia arriba) -> pagina vista (y hacia abajo) -> espacio PDF
        const m = mupdf.Matrix.concat([dir[0], dir[1], dir[1], -dir[0], x, y], inv);
        ops += `/${clave} ${num(c.tam)} Tf ${m.map(num).join(" ")} Tm <${hexWinAnsi(ln)}> Tj\n`;
      });
      ops += "ET Q\n";
      void i;
    }
    propios.put("Font", dicFuentes);
    obj.put("Resources", propios);
    if (ops) {
      const nuevo = d.addStream("q\n" + ops + "Q\n", {});
      const cont = obj.get("Contents");
      // el contenido viejo va envuelto en q/Q para que su estado no afecte al texto nuevo
      const lista2 = d.newArray();
      lista2.push(d.addStream("q\n", {}));
      if (cont.isArray()) cont.forEach((v) => lista2.push(v)); else if (!cont.isNull()) lista2.push(cont);
      lista2.push(d.addStream("Q\n", {}));
      lista2.push(nuevo);
      obj.put("Contents", lista2);
    }
    pag.destroy?.();
  }
  const buf = d.saveToBuffer("garbage=compact,compress=yes");
  const out = buf.asUint8Array().slice();
  buf.destroy?.();
  d.destroy?.();
  return out;
}
