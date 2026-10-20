/* ZUMBI SURVIVAL - etapa 1 - Game Boy Color - GBDK-2020 */
#include <gb/gb.h>
#include <gb/cgb.h>
#include <gb/font.h>
#include <gb/console.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <rand.h>

#define WC 128
#define NZ 10
#define MAXMOD 48
#define SPR0 166
#define SRAM ((uint8_t *)0xA000)
enum { T_GRASS, T_TREE, T_ROAD, T_WALL, T_FLOOR, T_CHEST, T_CHESTO, T_BENCH, T_STICK, T_STONE, T_TREEB, T_WATER };
#define ICON(i) (11 + (i))
#define T_DIG 23
#define T_HF 33
#define T_HH 34
#define T_HE 35
#define T_BLK 36
#define T_MARK 37

static const uint16_t PAL[8][4] = {
 {RGB(11,22,9),RGB(8,17,7),RGB(5,12,6),RGB(20,13,6)},
 {RGB(13,13,14),RGB(11,12,13),RGB(9,10,11),RGB(27,24,7)},
 {RGB(21,12,9),RGB(17,10,7),RGB(11,6,5),RGB(27,21,8)},
 {RGB(22,17,11),RGB(19,14,9),RGB(13,8,4),RGB(28,22,6)},
 {RGB(11,22,9),RGB(8,17,7),RGB(17,17,19),RGB(12,8,3)},
 {RGB(2,3,2),RGB(27,29,24),RGB(28,7,7),RGB(28,24,6)},
 {RGB(29,6,6),RGB(8,17,7),RGB(5,12,6),RGB(20,13,6)},
 {RGB(17,24,30),RGB(7,14,25),RGB(4,9,20),RGB(26,30,31)} };
static const uint16_t P_TEXT[4] = {RGB(1,2,1),RGB(6,10,6),RGB(18,24,16),RGB(27,30,23)};
static const uint16_t SPAL[3][4] = {
 {0,RGB(30,25,20),RGB(11,14,8),RGB(6,5,9)},
 {0,RGB(16,21,12),RGB(13,11,9),RGB(6,6,9)},
 {0,RGB(31,28,12),RGB(28,18,6),RGB(31,31,31)} };

typedef struct { uint8_t id, n; } Slot;
typedef struct { int16_t x, y, tx, ty; int8_t hp; uint8_t st, t, cd, wd, acc, stk, dv; int8_t wx, wy; } Zom;

static uint16_t seed;
static char name[8];
static uint8_t gender, volA = 5, volW = 6, volZ = 5;
static uint8_t kcur, kprev, cur_slot;
static Slot inv[18], crf[4], hand;
static uint8_t mx[MAXMOD], my[MAXMOD], mt[MAXMOD], nmod;
static int16_t tx0, ty0, px, py, camx, camy, lcx, lcy;
static int8_t fx, fy, hp;
static uint8_t sel, jz, jp, cd, inv_t, bh, steps, wk, run, dirty, chop_n;
static int16_t chop_x, chop_y;
static Zom zs[NZ];
static int16_t bx, by;
static int8_t bvx, bvy;
static uint8_t bl;

static int16_t iabs(int16_t a) { return a < 0 ? -a : a; }
static int8_t sgn(int16_t a) { return a > 0 ? 1 : (a < 0 ? -1 : 0); }
static uint16_t dist(int16_t a, int16_t b) { uint16_t d = iabs(a), e = iabs(b); return d > e ? d + (e >> 1) : e + (d >> 1); }
static uint8_t keys(void) { kprev = kcur; kcur = joypad(); return kcur & ~kprev; }

static uint8_t hsh(int16_t x, int16_t y, uint16_t s) {
 uint16_t h = s ^ ((uint16_t)x * 251u) ^ ((uint16_t)y * 1021u);
 h = (h ^ (h >> 5)) * 2053u; h ^= h >> 9; h *= 77u; h ^= h >> 7;
 return (uint8_t)(h ^ (h >> 8));
}

/* ---------- mundo ---------- */
static uint8_t treeraw(int16_t x, int16_t y) {
 uint8_t d = hsh(x >> 3, y >> 3, seed + 7) & 7;
 return hsh(x, y, seed) < (uint8_t)(8 + d * 6);
}
static uint8_t tile_at(int16_t x, int16_t y) {
 uint8_t i, v; int16_t rx, ry, b;
 if (x < 1 || y < 1 || x >= WC - 1 || y >= WC - 1) return T_TREEB;
 for (i = 0; i < nmod; i++) if (mx[i] == x && my[i] == y) return mt[i];
 rx = x - tx0; ry = y - ty0;
 if (rx >= 0 && rx < 36 && ry >= 0 && ry < 20) {
  for (i = 0; i < 3; i++) {
   b = 2 + i * 12;
   if (rx >= b && rx < b + 8 && ry >= 2 && ry < 9) {
    if (ry == 8 && (rx == b + 3 || rx == b + 4)) return T_FLOOR;
    if (rx == b || rx == b + 7 || ry == 2 || ry == 8) return T_WALL;
    if (ry == 3 && rx == b + 3) return T_CHEST;
    return T_FLOOR;
   }
  }
  return T_ROAD;
 }
 v = (uint8_t)((y + (seed & 63)) & 63); if (v > 32) v = 64 - v;
 if (iabs(x - 48 - (v >> 2)) <= 1) return T_WATER;
 v = hsh(x + 301, y + 77, seed);
 if (iabs(x - 64) < 6 && iabs(y - 64) < 6) return v < 30 ? T_STICK : (v < 60 ? T_STONE : T_GRASS);
 if (treeraw(x, y) && !treeraw(x - 1, y) && !treeraw(x, y - 1)) return hsh(x, y, seed + 11) < 100 ? T_TREE : T_TREEB;
 if (v < 6) return T_STICK;
 if (v < 10) return T_STONE;
 return T_GRASS;
}
static uint8_t solid(int16_t x, int16_t y) {
 uint8_t t = tile_at(x >> 3, y >> 3);
 return t == T_TREE || t == T_TREEB || t == T_WATER || t == T_WALL || t == T_CHEST || t == T_CHESTO || t == T_BENCH;
}
static uint8_t sbox(int16_t x, int16_t y) { return solid(x - 3, y - 3) || solid(x + 3, y - 3) || solid(x - 3, y) || solid(x + 3, y); }
static uint8_t zsolid(int16_t x, int16_t y) { return solid(x - 3, y - 2) || solid(x + 3, y - 2) || solid(x - 3, y + 1) || solid(x + 3, y + 1); }

static uint8_t pal_of(uint8_t id) { static const uint8_t m[12] = {0,6,1,2,3,3,3,3,4,4,0,7}; return id < 12 ? m[id] : 5; }
static void put(uint8_t x, uint8_t y, uint8_t id) {
 VBK_REG = 0; set_bkg_tile_xy(x, y, 128 + id);
 VBK_REG = 1; set_bkg_tile_xy(x, y, pal_of(id));
 VBK_REG = 0;
}
static void wput(uint8_t x, uint8_t y, uint8_t id) {
 VBK_REG = 0; set_win_tile_xy(x, y, 128 + id);
 VBK_REG = 1; set_win_tile_xy(x, y, 5);
 VBK_REG = 0;
}
static void set_mod(int16_t x, int16_t y, uint8_t t) {
 uint8_t i, f = 0;
 for (i = 0; i < nmod; i++) if (mx[i] == x && my[i] == y) { mt[i] = t; f = 1; }
 if (!f && nmod < MAXMOD) { mx[nmod] = (uint8_t)x; my[nmod] = (uint8_t)y; mt[nmod] = t; nmod++; }
 put((uint8_t)(x & 31), (uint8_t)(y & 31), t);
}
static void draw_cell(int16_t x, int16_t y) { put((uint8_t)(x & 31), (uint8_t)(y & 31), tile_at(x, y)); }
static void draw_col(int16_t x, int16_t y0) { uint8_t r; for (r = 0; r < 19; r++) draw_cell(x, y0 + r); }
static void draw_row(int16_t y, int16_t x0) { uint8_t c; for (c = 0; c < 21; c++) draw_cell(x0 + c, y); }
static void cam_update(void) {
 int16_t ncx, ncy;
 camx = px - 80; camy = py - 68;
 ncx = camx >> 3; ncy = camy >> 3;
 while (ncx > lcx) { lcx++; draw_col(lcx + 20, lcy); }
 while (ncx < lcx) { lcx--; draw_col(lcx, lcy); }
 while (ncy > lcy) { lcy++; draw_row(lcy + 18, lcx); }
 while (ncy < lcy) { lcy--; draw_row(lcy, lcx); }
 SCX_REG = (uint8_t)(camx & 255); SCY_REG = (uint8_t)(camy & 255);
}

/* ---------- gráficos gerados por código ---------- */
static uint8_t tb[8][8], sb[16][8];
static void tclr(uint8_t c) { memset(tb, c, 64); }
static void tr(uint8_t x, uint8_t y, uint8_t w, uint8_t h, uint8_t c) { uint8_t i, j; for (j = y; j < y + h && j < 8; j++) for (i = x; i < x + w && i < 8; i++) tb[j][i] = c; }
static void tput(uint8_t id) {
 uint8_t d[16], r, c, lo, hi;
 for (r = 0; r < 8; r++) { lo = 0; hi = 0; for (c = 0; c < 8; c++) { lo = (uint8_t)((lo << 1) | (tb[r][c] & 1)); hi = (uint8_t)((hi << 1) | ((tb[r][c] >> 1) & 1)); } d[r * 2] = lo; d[r * 2 + 1] = hi; }
 set_bkg_data(128 + id, 1, d);
}
static void sr(uint8_t x, uint8_t y, uint8_t w, uint8_t h, uint8_t c) { uint8_t i, j; for (j = y; j < y + h && j < 16; j++) for (i = x; i < x + w && i < 8; i++) sb[j][i] = c; }
static void sput(uint8_t f) {
 uint8_t d[32], r, c, lo, hi, t;
 for (t = 0; t < 2; t++) for (r = 0; r < 8; r++) {
  lo = 0; hi = 0;
  for (c = 0; c < 8; c++) { lo = (uint8_t)((lo << 1) | (sb[t * 8 + r][c] & 1)); hi = (uint8_t)((hi << 1) | ((sb[t * 8 + r][c] >> 1) & 1)); }
  d[t * 16 + r * 2] = lo; d[t * 16 + r * 2 + 1] = hi;
 }
 set_sprite_data(SPR0 + f * 2, 2, d);
}
static void init_bg(void) {
 static const uint8_t dg[10][5] = {{7,5,5,5,7},{2,6,2,2,7},{7,1,7,4,7},{7,1,7,1,7},{5,5,7,1,1},{7,4,7,1,7},{7,4,7,5,7},{7,1,1,1,1},{7,5,7,5,7},{7,5,7,1,7}};
 uint8_t i, j, id;
 tclr(1); tb[1][2] = 0; tb[5][6] = 0; tb[3][5] = 2; tb[6][1] = 2; tb[2][6] = 0; tput(T_GRASS);
 tclr(1); tr(1,0,6,5,2); tr(2,5,4,1,2); tr(2,1,3,2,1); tb[2][2] = 0; tb[3][5] = 0; tb[1][4] = 0; tb[4][3] = 0; tr(3,6,2,2,3); tput(T_TREE);
 tclr(1); tr(1,0,6,5,2); tr(2,5,4,1,2); tr(2,1,2,1,0); tr(3,6,2,2,3); tput(T_TREEB);
 tclr(1); tb[2][1] = 0; tb[2][2] = 0; tb[5][4] = 0; tb[5][5] = 0; tb[3][6] = 0; tb[7][1] = 0; tput(T_WATER);
 tclr(1); tb[2][3] = 2; tb[5][6] = 2; tb[1][6] = 0; tb[6][2] = 0; tput(T_ROAD);
 tclr(1); tr(0,3,8,1,2); tr(0,7,8,1,2); tr(3,0,1,3,2); tr(1,4,1,3,2); tr(5,4,1,3,2); tput(T_WALL);
 tclr(1); tr(0,3,8,1,2); tr(0,7,8,1,2); tr(5,0,1,3,2); tr(2,4,1,3,2); tb[1][1] = 0; tput(T_FLOOR);
 tclr(1); tr(1,2,6,5,2); tr(1,2,6,2,0); tr(3,2,1,5,3); tb[4][4] = 3; tput(T_CHEST);
 tclr(1); tr(1,1,6,1,0); tr(1,3,6,4,2); tr(2,3,4,2,3); tput(T_CHESTO);
 tclr(2); tr(0,1,8,4,0); tr(0,1,8,1,3); tr(1,5,1,3,1); tr(6,5,1,3,1); tput(T_BENCH);
 tclr(1); for (i = 1; i < 7; i++) tb[7 - i][i] = 3; tb[3][2] = 3; tput(T_STICK);
 tclr(1); tr(2,4,4,3,2); tr(3,3,2,1,2); tr(2,6,4,1,3); tput(T_STONE);
 for (id = 1; id <= 11; id++) {
  tclr(0);
  switch (id) {
   case 1: for (i = 1; i < 7; i++) tb[7 - i][i] = 3; break;
   case 2: tr(2,3,4,3,1); tr(3,6,2,1,3); break;
   case 3: tr(1,2,6,4,3); tr(5,3,2,2,1); break;
   case 4: for (i = 1; i < 7; i++) tb[7 - i][i] = 3; tr(4,1,3,2,1); break;
   case 5: tr(0,2,8,3,3); tr(1,5,1,3,3); tr(6,5,1,3,3); break;
   case 6: tr(3,1,2,5,1); tr(3,6,2,2,3); break;
   case 7: tr(1,3,2,4,3); tr(5,3,2,4,3); tr(1,2,2,1,1); tr(5,2,2,1,1); break;
   case 8: tr(1,2,6,2,1); tr(1,4,2,3,1); break;
   case 9: tr(2,2,4,5,2); tr(2,2,4,1,1); break;
   case 10: tr(2,2,4,4,2); tb[3][3] = 3; tb[4][5] = 3; tb[1][4] = 1; break;
   default: tr(2,2,4,4,2); tb[3][3] = 1; tb[3][4] = 1; tb[1][4] = 1; tb[6][3] = 3; break;
  }
  tput(ICON(id));
 }
 for (i = 0; i < 10; i++) {
  tclr(0);
  for (j = 0; j < 5; j++) { if (dg[i][j] & 4) tb[1 + j][2] = 1; if (dg[i][j] & 2) tb[1 + j][3] = 1; if (dg[i][j] & 1) tb[1 + j][4] = 1; }
  tput(T_DIG + i);
 }
 tclr(0); tr(1,1,2,1,2); tr(4,1,2,1,2); tr(0,2,7,2,2); tr(1,4,5,1,2); tr(2,5,3,1,2); tr(3,6,1,1,2); tput(T_HF);
 for (j = 1; j < 7; j++) for (i = 4; i < 7; i++) if (tb[j][i] == 2) tb[j][i] = 1;
 tput(T_HH);
 for (j = 1; j < 7; j++) for (i = 0; i < 7; i++) if (tb[j][i] == 2) tb[j][i] = 1;
 tput(T_HE);
 tclr(0); tput(T_BLK);
 tclr(0); tr(3,2,2,1,3); tr(2,3,4,1,3); tput(T_MARK);
}
static void mkspr(uint8_t f, uint8_t v, uint8_t s, uint8_t z) {
 memset(sb, 0, sizeof(sb));
 if (!z) {
  sr(1,0,6,2,3); sr(1,2,6,1,3);
  if (v == 0) { sr(2,3,4,3,1); sb[4][2] = 3; sb[4][5] = 3; }
  else if (v == 1) { sr(1,3,6,3,3); }
  else { sr(1,3,4,3,1); sr(5,3,2,3,3); sb[4][2] = 3; }
  if (v == 2) { sr(2,6,4,5,2); sr(5,6,2,4,3); sr(3,7,2,3,1); }
  else { sr(1,6,6,5,2); sr(0,6,1,4,2); sr(7,6,1,4,2); sb[10][0] = 1; sb[10][7] = 1; if (v == 1) sr(2,6,4,4,3); }
 } else {
  sr(2,0,4,2,3); sr(2,2,4,4,1);
  if (v == 0) { sb[4][2] = 3; sb[4][5] = 3; sb[5][3] = 3; sb[5][4] = 3; }
  else if (v == 2) { sb[4][2] = 3; sb[5][2] = 3; }
  sr(1,6,6,5,2);
  if (v == 2) sr(0,6,3,2,1); else { sr(0,5,1,4,1); sr(7,5,1,4,1); }
 }
 if (v == 2) { if (s) { sr(2,11,2,5,3); sr(5,11,2,4,3); } else { sr(3,11,2,5,3); sr(4,11,2,4,3); } }
 else { if (s) { sr(2,11,2,5,3); sr(4,11,2,4,3); } else { sr(2,11,2,4,3); sr(4,11,2,5,3); } }
 sput(f);
}
static void init_spr(void) {
 uint8_t v, s;
 for (v = 0; v < 3; v++) for (s = 0; s < 2; s++) { mkspr(v * 2 + s, v, s, 0); mkspr(6 + v * 2 + s, v, s, 1); }
 memset(sb, 0, sizeof(sb)); sr(3,7,2,2,1); sr(3,7,1,1,3); sput(12);
 set_sprite_palette(0, 3, &SPAL[0][0]);
}
static void spr(uint8_t nb, int16_t x, int16_t y, uint8_t frame, uint8_t prop) {
 int16_t sx = x - camx + 4, sy = y - camy;
 if (sx <= 0 || sx >= 168 || sy <= 0 || sy >= 160) { move_sprite(nb, 0, 0); return; }
 set_sprite_tile(nb, SPR0 + frame * 2); set_sprite_prop(nb, prop);
 move_sprite(nb, (uint8_t)sx, (uint8_t)sy);
}

/* ---------- som ---------- */
static void snd_init(void) { NR52_REG = 0x80; NR50_REG = 0x77; NR51_REG = 0xFF; }
static void sfx_w(uint8_t k) { uint8_t v = volW * 2; if (!v) return; NR10_REG = k ? 0x00 : 0x1F; NR11_REG = 0x80; NR12_REG = (uint8_t)((v << 4) | 3); NR13_REG = 0x00; NR14_REG = k ? 0x86 : 0x85; }
static void sfx_z(void) { uint8_t v = volZ * 2; if (!v) return; NR41_REG = 0x10; NR42_REG = (uint8_t)((v << 4) | 4); NR43_REG = 0x6B; NR44_REG = 0x80; }
static void note(uint8_t n) { static const uint16_t f[4] = {857, 1048, 711, 982}; uint8_t v = volA * 2; if (!v) return; NR21_REG = 0x80; NR22_REG = (uint8_t)((v << 4) | 5); NR23_REG = (uint8_t)(f[n & 3] & 255); NR24_REG = (uint8_t)(0x80 | (f[n & 3] >> 8)); }

/* ---------- inventário ---------- */
static uint8_t maxs(uint8_t id) { return (id == 4 || id == 6 || id == 8) ? 1 : 32; }
static uint8_t add(uint8_t id, uint8_t n) {
 uint8_t i, m = maxs(id), k;
 for (i = 0; i < 18 && n; i++) if (inv[i].id == id && inv[i].n < m) { k = m - inv[i].n; if (k > n) k = n; inv[i].n += k; n -= k; }
 for (i = 0; i < 18 && n; i++) if (!inv[i].id) { k = n < m ? n : m; inv[i].id = id; inv[i].n = k; n -= k; }
 dirty = 1; return n == 0;
}
static uint8_t take(uint8_t id) {
 uint8_t i;
 for (i = 0; i < 18; i++) if (inv[i].id == id) { if (--inv[i].n == 0) inv[i].id = 0; dirty = 1; return 1; }
 return 0;
}
static Slot *slot_of(uint8_t c) { return c < 18 ? &inv[c] : &crf[c - 18]; }
static uint8_t recipe(void) {
 if (crf[0].id == 2 && crf[1].id == 2 && crf[2].id == 1 && crf[3].id == 1) return 4;
 if (crf[0].id == 3 && crf[1].id == 3 && crf[2].id == 3 && crf[3].id == 3) return 5;
 return 0;
}
static void inv_act(uint8_t c, uint8_t half) {
 Slot *s, t; uint8_t o, m, k;
 if (c == 22) {
  o = recipe(); if (!o) return;
  if (hand.id && (hand.id != o || hand.n >= maxs(o))) return;
  for (k = 0; k < 4; k++) if (crf[k].id) { if (--crf[k].n == 0) crf[k].id = 0; }
  if (!hand.id) { hand.id = o; hand.n = 1; } else hand.n++;
  return;
 }
 s = slot_of(c);
 if (half) {
  if (!hand.id) { if (s->id) { k = (s->n + 1) / 2; hand.id = s->id; hand.n = k; s->n -= k; if (!s->n) s->id = 0; } }
  else if (!s->id || (s->id == hand.id && s->n < maxs(hand.id))) { s->id = hand.id; s->n++; hand.n--; if (!hand.n) hand.id = 0; }
  return;
 }
 if (!hand.id) { hand = *s; s->id = 0; s->n = 0; }
 else if (!s->id) { *s = hand; hand.id = 0; hand.n = 0; }
 else if (s->id == hand.id && maxs(s->id) > 1) { m = maxs(s->id) - s->n; k = hand.n < m ? hand.n : m; s->n += k; hand.n -= k; if (!hand.n) hand.id = 0; }
 else { t = *s; *s = hand; hand = t; }
}

/* ---------- telas de texto ---------- */
static const char *INAME[12] = {"", "GRAVETO", "PEDRA", "MADEIRA", "MACHADINHA", "BANCADA", "FACA", "MUNICAO", "PISTOLA", "COMIDA", "MACA SUJA", "MACA LAVADA"};
static const char ICODE[13] = "?GPMCBFUTOAL";
static void enter_text(void) {
 HIDE_SPRITES; HIDE_WIN; SCX_REG = 0; SCY_REG = 0;
 set_bkg_palette(0, 1, P_TEXT);
 VBK_REG = 1; fill_bkg_rect(0, 0, 32, 32, 0); VBK_REG = 0;
 cls();
}
static void cpos(uint8_t c, uint8_t *x, uint8_t *y) {
 if (c < 6) { *x = 3 + (c % 3) * 4; *y = 12 + c / 3; }
 else if (c < 18) { *x = 3 + ((c - 6) % 4) * 4; *y = 8 + (c - 6) / 4; }
 else if (c < 22) { *x = 2 + ((c - 18) & 1) * 6; *y = 3 + ((c - 18) >> 1) * 2; }
 else { *x = 14; *y = 4; }
}
static void dslot(uint8_t c, uint8_t curs) {
 uint8_t x, y; Slot s;
 cpos(c, &x, &y);
 if (c == 22) { s.id = recipe(); s.n = s.id ? 1 : 0; } else s = *slot_of(c);
 gotoxy(x - 1, y); printf(curs ? ">" : " ");
 gotoxy(x, y); printf("   ");
 gotoxy(x, y);
 if (!s.id) printf("--"); else if (s.n > 1) printf("%c%u", ICODE[s.id], (unsigned int)s.n); else printf("%c", ICODE[s.id]);
}
static void inv_draw(uint8_t c) {
 uint8_t i; Slot s;
 for (i = 0; i < 23; i++) dslot(i, i == c);
 gotoxy(0, 14); printf("MAO: ");
 gotoxy(5, 14); printf("               ");
 gotoxy(5, 14); if (hand.id) printf("%s X%u", INAME[hand.id], (unsigned int)hand.n); else printf("NADA");
 gotoxy(0, 15); printf("                    ");
 gotoxy(0, 15);
 if (c == 22) { i = recipe(); s.id = i; } else s = *slot_of(c);
 if (c == 22) { if (i) printf("PEGAR %s", INAME[i]); } else if (s.id) printf("%s", INAME[s.id]);
}
static uint8_t nav(uint8_t c, int8_t dx, int8_t dy) {
 uint8_t i, bx_, by_, x, y, best = c; int16_t ddx, ddy, sc, bs = 9999;
 cpos(c, &bx_, &by_);
 for (i = 0; i < 23; i++) {
  cpos(i, &x, &y); ddx = (int16_t)x - bx_; ddy = (int16_t)y - by_;
  if (dx && ddx * dx <= 0) continue;
  if (dy && ddy * dy <= 0) continue;
  sc = dx ? iabs(ddx) * 4 + iabs(ddy) : iabs(ddy) * 4 + iabs(ddx);
  if (sc < bs) { bs = sc; best = i; }
 }
 return best;
}
static void inventory(void) {
 uint8_t c = 0, pr, i;
 enter_text();
 gotoxy(0, 0); printf("INVENTARIO");
 gotoxy(0, 2); printf("CRAFT"); gotoxy(11, 4); printf("=>");
 gotoxy(0, 7); printf("MOCHILA"); gotoxy(0, 11); printf("HOTBAR");
 gotoxy(0, 16); printf("A PEGA  SEL METADE"); gotoxy(0, 17); printf("B FECHA");
 inv_draw(c);
 for (;;) {
  wait_vbl_done(); pr = keys();
  if (pr & J_B) break;
  if (pr & J_LEFT) { c = nav(c, -1, 0); inv_draw(c); }
  if (pr & J_RIGHT) { c = nav(c, 1, 0); inv_draw(c); }
  if (pr & J_UP) { c = nav(c, 0, -1); inv_draw(c); }
  if (pr & J_DOWN) { c = nav(c, 0, 1); inv_draw(c); }
  if (pr & J_A) { inv_act(c, 0); inv_draw(c); }
  if (pr & J_SELECT) { inv_act(c, 1); inv_draw(c); }
 }
 for (i = 0; i < 4; i++) if (crf[i].id) { add(crf[i].id, crf[i].n); crf[i].id = 0; crf[i].n = 0; }
 if (hand.id) { add(hand.id, hand.n); hand.id = 0; hand.n = 0; }
 dirty = 1;
}

/* ---------- salvar / carregar ---------- */
static void save_game(uint8_t s) {
 uint8_t *p = SRAM + (uint16_t)s * 256; uint8_t i;
 ENABLE_RAM;
 p[0] = 0x5A; for (i = 0; i < 8; i++) p[1 + i] = (uint8_t)name[i];
 p[9] = gender; p[10] = (uint8_t)(seed & 255); p[11] = (uint8_t)(seed >> 8);
 p[12] = (uint8_t)(px & 255); p[13] = (uint8_t)(px >> 8); p[14] = (uint8_t)(py & 255); p[15] = (uint8_t)(py >> 8);
 p[16] = (uint8_t)hp; p[17] = nmod;
 for (i = 0; i < 18; i++) { p[18 + 2 * i] = inv[i].id; p[19 + 2 * i] = inv[i].n; }
 for (i = 0; i < nmod; i++) { p[56 + 3 * i] = mx[i]; p[57 + 3 * i] = my[i]; p[58 + 3 * i] = mt[i]; }
 DISABLE_RAM;
}
static uint8_t load_game(uint8_t s) {
 uint8_t *p = SRAM + (uint16_t)s * 256; uint8_t i, ok;
 ENABLE_RAM;
 ok = (p[0] == 0x5A);
 if (ok) {
  for (i = 0; i < 8; i++) name[i] = (char)p[1 + i];
  gender = p[9]; seed = (uint16_t)p[10] | ((uint16_t)p[11] << 8);
  px = (int16_t)((uint16_t)p[12] | ((uint16_t)p[13] << 8)); py = (int16_t)((uint16_t)p[14] | ((uint16_t)p[15] << 8));
  hp = (int8_t)p[16]; nmod = p[17]; if (nmod > MAXMOD) nmod = MAXMOD;
  for (i = 0; i < 18; i++) { inv[i].id = p[18 + 2 * i]; inv[i].n = p[19 + 2 * i]; }
  for (i = 0; i < nmod; i++) { mx[i] = p[56 + 3 * i]; my[i] = p[57 + 3 * i]; mt[i] = p[58 + 3 * i]; }
 }
 DISABLE_RAM;
 return ok;
}
static uint8_t slot_used(uint8_t s) { uint8_t r; ENABLE_RAM; r = SRAM[(uint16_t)s * 256] == 0x5A; DISABLE_RAM; return r; }
static void kill_save(uint8_t s) { ENABLE_RAM; SRAM[(uint16_t)s * 256] = 0; DISABLE_RAM; }
static void save_profile(void) {
 uint8_t *p = SRAM + 768; uint8_t i;
 ENABLE_RAM; p[0] = 0xA5; for (i = 0; i < 8; i++) p[1 + i] = (uint8_t)name[i];
 p[9] = gender; p[10] = volA; p[11] = volW; p[12] = volZ; DISABLE_RAM;
}
static uint8_t load_profile(void) {
 uint8_t *p = SRAM + 768; uint8_t i, ok;
 ENABLE_RAM; ok = (p[0] == 0xA5);
 if (ok) { for (i = 0; i < 8; i++) name[i] = (char)p[1 + i]; gender = p[9]; volA = p[10] & 7; volW = p[11] & 7; volZ = p[12] & 7; name[7] = 0; }
 DISABLE_RAM; return ok;
}

/* ---------- menus ---------- */
static void ask_name(void) {
 uint8_t i, pos = 0, pr; char ch[7];
 for (i = 0; i < 6; i++) ch[i] = 'A'; ch[6] = 0;
 enter_text();
 gotoxy(2, 2); printf("QUAL O SEU NOME?");
 gotoxy(2, 11); printf("CIMA/BAIXO: LETRA"); gotoxy(2, 12); printf("DIREITA: PROXIMA");
 gotoxy(2, 13); printf("ESQUERDA: VOLTAR"); gotoxy(2, 14); printf("START: PRONTO");
 for (;;) {
  gotoxy(7, 6); printf("%s", ch);
  gotoxy(7, 7); printf("       "); gotoxy(7 + pos, 7); printf("^");
  wait_vbl_done(); pr = keys();
  if (pr & J_UP) { ch[pos] = (ch[pos] == ' ') ? 'A' : (ch[pos] == 'Z' ? ' ' : ch[pos] + 1); }
  if (pr & J_DOWN) { ch[pos] = (ch[pos] == 'A') ? ' ' : (ch[pos] == ' ' ? 'Z' : ch[pos] - 1); }
  if ((pr & J_RIGHT) || (pr & J_A)) { if (pos < 5) pos++; }
  if ((pr & J_LEFT) || (pr & J_B)) { if (pos > 0) pos--; }
  if (pr & J_START) break;
 }
 for (i = 0; i < 6; i++) name[i] = ch[i];
 name[6] = 0; name[7] = 0;
 for (i = 5; i > 0 && name[i] == ' '; i--) name[i] = 0;
}
static void ask_gender(void) {
 uint8_t c = 0, pr, i;
 static const char *G[3] = {"MASCULINO", "FEMININO", "OUTRO"};
 enter_text(); gotoxy(2, 3); printf("QUAL O SEU GENERO?");
 for (;;) {
  for (i = 0; i < 3; i++) { gotoxy(5, 7 + i * 2); printf("%s", G[i]); gotoxy(3, 7 + i * 2); printf(i == c ? ">" : " "); }
  wait_vbl_done(); pr = keys();
  if ((pr & J_DOWN) && c < 2) c++;
  if ((pr & J_UP) && c > 0) c--;
  if (pr & (J_A | J_START)) break;
 }
 gender = c;
}
static void options(void) {
 uint8_t c = 0, pr, i, j; uint8_t *v[3];
 static const char *L[3] = {"AUDIO", "ARMAS", "ZUMBIS"};
 v[0] = &volA; v[1] = &volW; v[2] = &volZ;
 enter_text(); gotoxy(6, 2); printf("OPCOES");
 for (;;) {
  for (i = 0; i < 3; i++) {
   gotoxy(2, 6 + i * 3); printf(i == c ? ">" : " "); printf("%s", L[i]);
   gotoxy(3, 7 + i * 3); for (j = 0; j < 8; j++) printf(j < *v[i] ? "#" : "-");
  }
  gotoxy(2, 16); printf("B: VOLTAR");
  wait_vbl_done(); pr = keys();
  if ((pr & J_DOWN) && c < 2) c++;
  if ((pr & J_UP) && c > 0) c--;
  if ((pr & J_RIGHT) && *v[c] < 7) { (*v[c])++; if (c == 0) note(0); if (c == 1) sfx_w(0); if (c == 2) sfx_z(); }
  if ((pr & J_LEFT) && *v[c] > 0) { (*v[c])--; if (c == 0) note(0); if (c == 1) sfx_w(0); if (c == 2) sfx_z(); }
  if (pr & (J_B | J_START)) break;
 }
 save_profile();
}
static uint8_t menu_main(void) {
 uint8_t c = 0, pr; uint16_t t = 0;
 enter_text(); gotoxy(3, 3); printf("ZUMBI SURVIVAL");
 gotoxy(4, 14); printf("OLA, %s", name);
 for (;;) {
  gotoxy(6, 8); printf("%cPLAY", c == 0 ? '>' : ' ');
  gotoxy(6, 10); printf("%cOPCOES", c == 1 ? '>' : ' ');
  wait_vbl_done(); t++; pr = keys();
  if ((pr & J_DOWN) && c == 0) c = 1;
  if ((pr & J_UP) && c == 1) c = 0;
  if (pr & (J_A | J_START)) break;
 }
 seed = (uint16_t)(t * 257u + DIV_REG);
 return c;
}

/* ---------- zumbis / barulho ---------- */
static void noise(int16_t x, int16_t y, uint8_t r) {
 uint8_t i; uint16_t lim = (uint16_t)r * 8;
 for (i = 0; i < NZ; i++) if (zs[i].hp > 0 && zs[i].st < 2 && dist(zs[i].x - x, zs[i].y - y) < lim) { zs[i].st = 1; zs[i].tx = x; zs[i].ty = y; zs[i].t = 200; }
}
static void spawn_all(void) {
 uint8_t i, n; int16_t cx, cy;
 for (i = 0; i < NZ; i++) {
  memset(&zs[i], 0, sizeof(Zom)); zs[i].hp = 6;
  if (i < 3) { zs[i].x = (tx0 + 2 + i * 12 + 4) * 8 + 4; zs[i].y = (ty0 + 5) * 8 + 4; continue; }
  for (n = 0; n < 30; n++) {
   cx = 6 + hsh(i, n, seed + 3) % 116; cy = 6 + hsh(n, i, seed + 5) % 116;
   if (iabs(cx - 64) > 14 || iabs(cy - 64) > 14) if (!zsolid(cx * 8 + 4, cy * 8 + 4)) break;
  }
  zs[i].x = cx * 8 + 4; zs[i].y = cy * 8 + 4;
 }
}
static void zupd(Zom *q) {
 int16_t dx, dy; uint16_t d; int8_t mvx = 0, mvy = 0; uint8_t sp = 0, moved;
 if (q->hp <= 0) return;
 dx = px - q->x; dy = py - q->y; d = dist(dx, dy);
 if (q->cd) q->cd--;
 if (q->st < 2 && d < 40) { q->st = 2; if (rand() < 60) sfx_z(); }
 if (q->st == 2) {
  if (d > 72) { q->st = 1; q->tx = px; q->ty = py; q->t = 200; }
  else { mvx = sgn(dx); mvy = sgn(dy); sp = 9; if (iabs(dx) < 3) mvx = 0; if (iabs(dy) < 3) mvy = 0; }
 } else if (q->st == 1) {
  dx = q->tx - q->x; dy = q->ty - q->y;
  if (dist(dx, dy) > 4 && q->t) { mvx = sgn(dx); mvy = sgn(dy); sp = 7; q->t--; } else q->st = 0;
 } else {
  if (q->wd == 0) { q->wd = 40 + rand() % 60; q->wx = (int8_t)(rand() % 3) - 1; q->wy = (int8_t)(rand() % 3) - 1; if (rand() % 3 == 0) { q->wx = 0; q->wy = 0; } }
  q->wd--; mvx = q->wx; mvy = q->wy; sp = 3;
 }
 q->acc += sp;
 while (q->acc >= 16) {
  q->acc -= 16; moved = 0;
  if (mvx && !zsolid(q->x + mvx, q->y)) { q->x += mvx; moved = 1; }
  if (mvy && !zsolid(q->x, q->y + mvy)) { q->y += mvy; moved = 1; }
  if (!moved && (mvx || mvy)) {
   if (++q->stk > 6) { q->wx = mvy; q->wy = mvx ? -mvx : 1; if (!q->wx && !q->wy) q->wx = 1; q->wd = 30; q->st = 0; q->stk = 0; }
  } else q->stk = 0;
 }
 if (mvx || mvy) { if (iabs(mvx) >= iabs(mvy) && mvx) q->dv = mvx < 0 ? 2 : 3; else q->dv = mvy < 0 ? 1 : 0; }
 if (d < 10 && jz < 4 && !q->cd && !inv_t) { hp--; q->cd = 50; inv_t = 40; dirty = 1; sfx_z(); }
}

/* ---------- jogo ---------- */
static void loot(void) {
 uint8_t got = 0;
 if (rand() < 40) { add(7, 2 + rand() % 3); got = 1; }
 if (rand() < 12) { add(8, 1); got = 1; }
 if (rand() < 100) { add(9, 1); got = 1; }
 if (rand() < 90) { add(1, 1); got = 1; }
 if (!got) add(9, 1);
}
static void do_attack(void) {
 uint8_t id = inv[sel].id, i, hit = 0, dmg, t; int16_t ax, ay, cx, cy;
 ax = px + fx * 9; ay = py - 3 + fy * 9; cx = ax >> 3; cy = ay >> 3;
 cd = 18; t = tile_at(cx, cy);
 if (id == 8) {
  if (take(7)) { bx = px; by = py - 6; bvx = fx * 3; bvy = fy * 3; bl = 40; sfx_w(0); noise(px, py, 14); } else { cd = 30; }
  return;
 }
 if (id == 10) {
  if (t == T_WATER) { if (--inv[sel].n == 0) inv[sel].id = 0; add(11, 1); sfx_w(1); }
  else { hp--; if (--inv[sel].n == 0) inv[sel].id = 0; sfx_z(); }
  dirty = 1; return;
 }
 if (id == 9 || id == 11) { if (hp < 10) { hp += 2; if (hp > 10) hp = 10; if (--inv[sel].n == 0) inv[sel].id = 0; dirty = 1; } return; }
 if (id == 5) { if (t == T_GRASS) { set_mod(cx, cy, T_BENCH); if (--inv[sel].n == 0) inv[sel].id = 0; dirty = 1; } return; }
 dmg = (id == 4) ? 2 : (id == 6 ? 3 : 1);
 for (i = 0; i < NZ; i++) if (zs[i].hp > 0 && dist(zs[i].x - ax, zs[i].y - 3 - ay) < 12) { zs[i].hp -= dmg; zs[i].x += fx * 5; zs[i].y += fy * 5; zs[i].st = 2; hit = 1; }
 if (hit) { sfx_w(1); sfx_z(); noise(px, py, 3); return; }
 if (t == T_TREE || t == T_TREEB) {
  if (id != 4) {
   if (t == T_TREE) {
    if (chop_x == cx && chop_y == cy) chop_n++; else { chop_x = cx; chop_y = cy; chop_n = 1; }
    sfx_w(1); noise(px, py, 3);
    if (chop_n >= 3) { set_mod(cx, cy, T_TREEB); add(10, 1 + (rand() & 1)); chop_n = 0; }
   }
  } else {
   if (chop_x == cx && chop_y == cy) chop_n++; else { chop_x = cx; chop_y = cy; chop_n = 1; }
   sfx_w(1); noise(px, py, 6);
   if (chop_n >= 4) { set_mod(cx, cy, T_GRASS); add(3, 2 + (rand() & 1)); if (rand() < 110) add(1, 1); chop_n = 0; }
  }
 } else if (t == T_CHEST) { set_mod(cx, cy, T_CHESTO); loot(); sfx_w(1); noise(px, py, 5); }
}
static void hud(void) {
 uint8_t i, n, id; int8_t h;
 for (i = 0; i < 6; i++) {
  id = inv[i].id; n = inv[i].n;
  wput(i * 3, 1, id ? ICON(id) : T_BLK);
  wput(i * 3 + 1, 1, n > 9 ? T_DIG + n / 10 : T_BLK);
  wput(i * 3 + 2, 1, n > 1 ? T_DIG + n % 10 : T_BLK);
  wput(i * 3, 0, i == sel ? T_MARK : T_BLK);
 }
 for (i = 0; i < 5; i++) { h = hp - 2 * i; wput(15 + i, 0, h >= 2 ? T_HF : (h == 1 ? T_HH : T_HE)); }
 dirty = 0;
}
static void enter_game(void) {
 uint8_t r, c;
 DISPLAY_OFF;
 set_bkg_palette(0, 8, &PAL[0][0]);
 VBK_REG = 1; fill_bkg_rect(0, 0, 32, 32, 0); VBK_REG = 0;
 camx = px - 80; camy = py - 68; lcx = camx >> 3; lcy = camy >> 3;
 for (r = 0; r < 19; r++) for (c = 0; c < 21; c++) draw_cell(lcx + c, lcy + r);
 SCX_REG = (uint8_t)(camx & 255); SCY_REG = (uint8_t)(camy & 255);
 for (c = 0; c < 20; c++) { wput(c, 0, T_BLK); wput(c, 1, T_BLK); }
 move_win(7, 128); SHOW_WIN; SHOW_BKG; SHOW_SPRITES; DISPLAY_ON;
 hud();
}
static void world_init(void) {
 tx0 = 76 + (seed & 7); ty0 = 20 + ((seed >> 3) & 31);
 initrand(seed * 3u + DIV_REG);
 spawn_all();
 hand.id = 0; hand.n = 0; memset(crf, 0, sizeof(crf));
 sel = 0; jp = 0; jz = 0; cd = 0; inv_t = 0; bh = 0; bl = 0; chop_n = 0; chop_x = -1; chop_y = -1; fx = 0; fy = 1;
}
static void play(uint8_t slot) {
 static const uint8_t jt[13] = {2,4,6,8,9,10,10,9,8,6,4,2,0};
 uint8_t i, pr, view, flip, pcell; int8_t dx, dy; uint8_t sp; uint16_t ft = 0; uint8_t mus = 0, nt = 0;
 cur_slot = slot; world_init(); enter_game();
 for (;;) {
  wait_vbl_done(); pr = keys(); ft++;
  if (pr & J_START) { inventory(); enter_game(); save_game(slot); continue; }
  if (pr & J_SELECT) { sel = (sel + 1) % 6; dirty = 1; }
  if (kcur & J_B) { if (bh < 255) bh++; }
  else { if ((kprev & J_B) && bh < 15 && jp == 0) { jp = 1; noise(px, py, 2); sfx_w(1); } bh = 0; }
  run = ((kcur & J_B) && bh >= 15) ? 1 : 0;
  if (jp) { jz = jt[jp - 1]; jp++; if (jp > 13) { jp = 0; jz = 0; noise(px, py, 3); } }
  dx = 0; dy = 0;
  if (kcur & J_LEFT) dx = -1; else if (kcur & J_RIGHT) dx = 1;
  if (kcur & J_UP) dy = -1; else if (kcur & J_DOWN) dy = 1;
  if (dx || dy) {
   sp = run ? 2 : 1;
   for (i = 0; i < sp; i++) { if (dx && !sbox(px + dx, py)) px += dx; if (dy && !sbox(px, py + dy)) py += dy; }
   if (!(kcur & J_A)) { fx = dx; fy = dy; }
   if (++steps >= (run ? 10 : 24)) { steps = 0; noise(px, py, run ? 7 : 2); }
   wk = (ft >> (run ? 2 : 3)) & 1;
  }
  if (cd) cd--;
  if ((kcur & J_A) && !cd) { do_attack(); dirty = 1; }
  if (inv_t) inv_t--;
  pcell = tile_at(px >> 3, (py - 2) >> 3);
  if (pcell == T_STICK || pcell == T_STONE) { if (add(pcell == T_STICK ? 1 : 2, 1)) set_mod(px >> 3, (py - 2) >> 3, T_GRASS); }
  if (bl) {
   bx += bvx; by += bvy; bl--;
   if (solid(bx, by)) bl = 0;
   for (i = 0; i < NZ; i++) if (zs[i].hp > 0 && dist(zs[i].x - bx, zs[i].y - 4 - by) < 8) { zs[i].hp -= 3; zs[i].st = 2; bl = 0; sfx_z(); }
  }
  for (i = 0; i < NZ; i++) zupd(&zs[i]);
  if (hp <= 0) break;
  if (dirty) hud();
  if (++mus >= 70) { mus = 0; nt++; note(nt); }
  if (ft % 900 == 0) save_game(slot);
  cam_update();
  if (fx == 0) { view = fy >= 0 ? 0 : 1; flip = 0; } else { view = 2; flip = fx > 0; }
  if (inv_t & 2) move_sprite(0, 0, 0); else spr(0, px, py - jz, view * 2 + wk, flip ? S_FLIPX : 0);
  if (bl) spr(1, bx, by, 12, 2); else move_sprite(1, 0, 0);
  for (i = 0; i < NZ; i++) {
   if (zs[i].hp <= 0) { move_sprite(2 + i, 0, 0); continue; }
   view = zs[i].dv == 1 ? 1 : (zs[i].dv >= 2 ? 2 : 0);
   spr(2 + i, zs[i].x, zs[i].y, 6 + view * 2 + ((ft >> 4) & 1), 1 | (zs[i].dv == 3 ? S_FLIPX : 0));
  }
 }
 kill_save(slot);
 enter_text(); gotoxy(4, 7); printf("VOCE MORREU"); gotoxy(2, 12); printf("APERTE START");
 waitpadup();
 do { wait_vbl_done(); } while (!(joypad() & J_START));
 waitpadup();
}
static void slot_menu(void) {
 uint8_t c = 0, pr, i, used;
 enter_text(); gotoxy(4, 2); printf("SEUS JOGOS");
 for (;;) {
  for (i = 0; i < 3; i++) {
   gotoxy(2, 6 + i * 3); printf("%c", i == c ? '>' : ' ');
   gotoxy(3, 6 + i * 3); printf("%u ", (unsigned int)(i + 1));
   if (slot_used(i)) printf("JOGAR     "); else printf("NOVO JOGO ");
  }
  gotoxy(1, 15); printf("A: ESCOLHER  B: VOLTAR"); gotoxy(1, 16); printf("SELECT: APAGAR");
  wait_vbl_done(); pr = keys();
  if ((pr & J_DOWN) && c < 2) c++;
  if ((pr & J_UP) && c > 0) c--;
  if (pr & J_B) return;
  if (pr & J_SELECT) { kill_save(c); }
  if (pr & J_A) {
   used = slot_used(c);
   if (used) { load_game(c); }
   else {
    load_profile();
    nmod = 0; memset(inv, 0, sizeof(inv));
    px = 64 * 8 + 4; py = 64 * 8 + 4; hp = 10;
   }
   play(c); return;
  }
 }
}

void main(void) {
 uint8_t ch;
 DISPLAY_OFF;
 font_init(); font_set(font_load(font_ibm));
 SPRITES_8x16;
 init_bg(); init_spr(); snd_init();
 SHOW_BKG; DISPLAY_ON;
 if (!load_profile()) { ask_name(); ask_gender(); save_profile(); }
 for (;;) {
  ch = menu_main();
  if (ch == 0) slot_menu(); else options();
 }
}
