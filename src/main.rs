use std::io::{self, BufRead};
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(not(target_arch = "wasm32"))]
use std::sync::mpsc;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

const EMPTY: i8 = 0;
const PAWN: i8 = 1;
const KNIGHT: i8 = 2;
const BISHOP: i8 = 3;
const ROOK: i8 = 4;
const QUEEN: i8 = 5;
const KING: i8 = 6;
const WHITE: i8 = 1;
const BLACK: i8 = -1;

const FLAG_CAPTURE: u32 = 1 << 15;
const FLAG_EP: u32 = 1 << 16;
const FLAG_CASTLE: u32 = 1 << 17;
const FLAG_DOUBLE: u32 = 1 << 18;
const FLAG_PROMO: u32 = 1 << 19;

const START_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
const INF: i32 = 32_000;
const MATE: i32 = 30_000;
const MAX_PLY: usize = 128;
const MAX_MOVES: usize = 256;
const PIECE_VALUE: [i32; 7] = [0, 100, 320, 330, 500, 950, 20_000];
const KNIGHT_DELTAS: [(i8, i8); 8] = [
    (1, 2),
    (2, 1),
    (2, -1),
    (1, -2),
    (-1, -2),
    (-2, -1),
    (-2, 1),
    (-1, 2),
];
const KING_DELTAS: [(i8, i8); 8] = [
    (1, 1),
    (1, 0),
    (1, -1),
    (0, 1),
    (0, -1),
    (-1, 1),
    (-1, 0),
    (-1, -1),
];
const BISHOP_DIRS: [(i8, i8); 4] = [(1, 1), (1, -1), (-1, 1), (-1, -1)];
const ROOK_DIRS: [(i8, i8); 4] = [(1, 0), (-1, 0), (0, 1), (0, -1)];

#[inline(always)]
fn file(sq: u8) -> i8 {
    (sq & 7) as i8
}
#[inline(always)]
fn rank(sq: u8) -> i8 {
    (sq >> 3) as i8
}
#[inline(always)]
fn square(f: i8, r: i8) -> Option<u8> {
    if (0..8).contains(&f) && (0..8).contains(&r) {
        Some((r * 8 + f) as u8)
    } else {
        None
    }
}
#[inline(always)]
fn color(piece: i8) -> i8 {
    if piece > 0 {
        WHITE
    } else if piece < 0 {
        BLACK
    } else {
        0
    }
}
#[inline(always)]
fn kind(piece: i8) -> i8 {
    piece.abs()
}

#[inline(always)]
fn encode_move(from: u8, to: u8, promo: i8, flags: u32) -> u32 {
    from as u32 | ((to as u32) << 6) | ((promo as u32) << 12) | flags
}
#[inline(always)]
fn move_from(mv: u32) -> u8 {
    (mv & 63) as u8
}
#[inline(always)]
fn move_to(mv: u32) -> u8 {
    ((mv >> 6) & 63) as u8
}
#[inline(always)]
fn move_promo(mv: u32) -> i8 {
    ((mv >> 12) & 7) as i8
}

#[derive(Clone)]
struct Zobrist {
    pieces: [[u64; 64]; 12],
    side: u64,
    castle: [u64; 16],
    ep: [u64; 8],
}

fn zobrist() -> &'static Zobrist {
    static Z: OnceLock<Zobrist> = OnceLock::new();
    Z.get_or_init(|| {
        fn next(x: &mut u64) -> u64 {
            *x = x.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = *x;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        let mut seed = 0xC0FFEE1234567890;
        let mut pieces = [[0; 64]; 12];
        for row in &mut pieces {
            for value in row {
                *value = next(&mut seed);
            }
        }
        let side = next(&mut seed);
        let mut castle = [0; 16];
        for value in &mut castle {
            *value = next(&mut seed);
        }
        let mut ep = [0; 8];
        for value in &mut ep {
            *value = next(&mut seed);
        }
        Zobrist {
            pieces,
            side,
            castle,
            ep,
        }
    })
}

#[inline(always)]
fn piece_index(piece: i8) -> usize {
    if piece > 0 {
        (piece - 1) as usize
    } else {
        (6 + (-piece - 1)) as usize
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Position {
    board: [i8; 64],
    side: i8,
    castle: u8,
    ep: i8,
    halfmove: u16,
    fullmove: u16,
    king_sq: [u8; 2],
    hash: u64,
    mg: i32,
    eg: i32,
    phase: i32,
}

#[derive(Clone, Copy)]
struct Undo {
    captured: i8,
    castle: u8,
    ep: i8,
    halfmove: u16,
    fullmove: u16,
    hash: u64,
    mg: i32,
    eg: i32,
    phase: i32,
    king_sq: [u8; 2],
}

impl Position {
    fn from_fen(fen: &str) -> Result<Self, String> {
        let fields: Vec<&str> = fen.split_whitespace().collect();
        if fields.len() != 6 {
            return Err("FEN requires exactly six fields".into());
        }
        let mut board = [EMPTY; 64];
        let mut r = 7i8;
        let mut f = 0i8;
        for ch in fields[0].chars() {
            if ch == '/' {
                if f != 8 || r == 0 {
                    return Err("invalid FEN board".into());
                }
                r -= 1;
                f = 0;
                continue;
            }
            if let Some(n) = ch.to_digit(10) {
                if n == 0 || n > 8 || f + n as i8 > 8 {
                    return Err("invalid FEN empty-square count".into());
                }
                f += n as i8;
                continue;
            }
            let piece = match ch.to_ascii_lowercase() {
                'p' => PAWN,
                'n' => KNIGHT,
                'b' => BISHOP,
                'r' => ROOK,
                'q' => QUEEN,
                'k' => KING,
                _ => return Err("invalid FEN piece".into()),
            } * if ch.is_ascii_uppercase() {
                WHITE
            } else {
                BLACK
            };
            if f >= 8 || r < 0 {
                return Err("invalid FEN placement".into());
            }
            board[(r * 8 + f) as usize] = piece;
            f += 1;
        }
        if r != 0 || f != 8 {
            return Err("incomplete FEN board".into());
        }
        let side = match fields[1] {
            "w" => WHITE,
            "b" => BLACK,
            _ => return Err("invalid side".into()),
        };
        if fields[2] != "-" {
            let mut seen = 0u8;
            for ch in fields[2].chars() {
                let bit = match ch {
                    'K' => 1,
                    'Q' => 2,
                    'k' => 4,
                    'q' => 8,
                    _ => return Err("invalid castling rights".into()),
                };
                if seen & bit != 0 {
                    return Err("duplicate castling right".into());
                }
                seen |= bit;
            }
        }
        let mut castle = 0u8;
        if fields[2].contains('K') {
            castle |= 1;
        }
        if fields[2].contains('Q') {
            castle |= 2;
        }
        if fields[2].contains('k') {
            castle |= 4;
        }
        if fields[2].contains('q') {
            castle |= 8;
        }
        let ep = if fields[3] == "-" {
            -1
        } else {
            parse_square(fields[3]).ok_or("invalid en passant")? as i8
        };
        let halfmove = fields
            .get(4)
            .map(|s| s.parse::<u16>().map_err(|_| "invalid halfmove clock"))
            .transpose()?
            .unwrap_or(0);
        let fullmove = fields
            .get(5)
            .map(|s| s.parse::<u16>().map_err(|_| "invalid fullmove number"))
            .transpose()?
            .unwrap_or(1);
        if fullmove == 0 {
            return Err("fullmove number must be positive".into());
        }
        let mut king_sq = [255; 2];
        let mut king_count = [0; 2];
        for sq in 0..64 {
            if board[sq] == KING {
                king_sq[0] = sq as u8;
                king_count[0] += 1;
            } else if board[sq] == -KING {
                king_sq[1] = sq as u8;
                king_count[1] += 1;
            }
        }
        if king_count != [1, 1] {
            return Err("FEN must contain exactly one king per side".into());
        }
        for (right, king, king_home, rook, rook_home) in [
            (1, KING, 4, ROOK, 7),
            (2, KING, 4, ROOK, 0),
            (4, -KING, 60, -ROOK, 63),
            (8, -KING, 60, -ROOK, 56),
        ] {
            if castle & right != 0 && (board[king_home] != king || board[rook_home] != rook) {
                return Err("castling right requires king and rook on home squares".into());
            }
        }
        if ep >= 0 {
            let target = ep as u8;
            let required_rank = if side == WHITE { 5 } else { 2 };
            let captured_sq = (target as i16 - side as i16 * 8) as usize;
            let origin_sq = (target as i16 + side as i16 * 8) as usize;
            if rank(target) != required_rank
                || board[target as usize] != EMPTY
                || board[captured_sq] != -side * PAWN
                || board[origin_sq] != EMPTY
                || halfmove != 0
            {
                return Err("invalid en passant state".into());
            }
        }
        let mut pos = Position {
            board,
            side,
            castle,
            ep,
            halfmove,
            fullmove,
            king_sq,
            hash: 0,
            mg: 0,
            eg: 0,
            phase: 0,
        };
        pos.recompute_state();
        Ok(pos)
    }

    fn recompute_state(&mut self) {
        self.hash = zobrist().castle[self.castle as usize];
        if self.side == BLACK {
            self.hash ^= zobrist().side;
        }
        self.mg = 0;
        self.eg = 0;
        self.phase = 0;
        for sq in 0..64u8 {
            let p = self.board[sq as usize];
            if p != EMPTY {
                self.hash ^= zobrist().pieces[piece_index(p)][sq as usize];
                let (mg, eg, phase) = piece_eval(p, sq);
                self.mg += mg;
                self.eg += eg;
                self.phase += phase;
            }
        }
        if let Some(ep_file) = self.ep_hash_file() {
            self.hash ^= zobrist().ep[ep_file];
        }
    }

    fn to_fen(&self) -> String {
        let mut board = String::new();
        for r in (0..8).rev() {
            let mut empty = 0;
            for f in 0..8 {
                let piece = self.board[r * 8 + f];
                if piece == EMPTY {
                    empty += 1;
                    continue;
                }
                if empty > 0 {
                    board.push(char::from_digit(empty, 10).unwrap());
                    empty = 0;
                }
                let symbol = match kind(piece) {
                    PAWN => 'p',
                    KNIGHT => 'n',
                    BISHOP => 'b',
                    ROOK => 'r',
                    QUEEN => 'q',
                    KING => 'k',
                    _ => unreachable!(),
                };
                board.push(if piece > 0 {
                    symbol.to_ascii_uppercase()
                } else {
                    symbol
                });
            }
            if empty > 0 {
                board.push(char::from_digit(empty, 10).unwrap());
            }
            if r > 0 {
                board.push('/');
            }
        }
        let mut rights = String::new();
        if self.castle & 1 != 0 {
            rights.push('K');
        }
        if self.castle & 2 != 0 {
            rights.push('Q');
        }
        if self.castle & 4 != 0 {
            rights.push('k');
        }
        if self.castle & 8 != 0 {
            rights.push('q');
        }
        if rights.is_empty() {
            rights.push('-');
        }
        let ep = if self.ep >= 0 {
            square_name(self.ep as u8)
        } else {
            "-".into()
        };
        format!(
            "{} {} {} {} {} {}",
            board,
            if self.side == WHITE { "w" } else { "b" },
            rights,
            ep,
            self.halfmove,
            self.fullmove
        )
    }

    #[inline(always)]
    fn king_of(&self, side: i8) -> u8 {
        self.king_sq[if side == WHITE { 0 } else { 1 }]
    }

    #[inline(always)]
    fn remove_piece(&mut self, sq: u8) -> i8 {
        let p = self.board[sq as usize];
        if p != EMPTY {
            self.hash ^= zobrist().pieces[piece_index(p)][sq as usize];
            let (mg, eg, phase) = piece_eval(p, sq);
            self.mg -= mg;
            self.eg -= eg;
            self.phase -= phase;
            self.board[sq as usize] = EMPTY;
        }
        p
    }

    #[inline(always)]
    fn add_piece(&mut self, sq: u8, p: i8) {
        self.board[sq as usize] = p;
        self.hash ^= zobrist().pieces[piece_index(p)][sq as usize];
        let (mg, eg, phase) = piece_eval(p, sq);
        self.mg += mg;
        self.eg += eg;
        self.phase += phase;
    }

    #[inline(always)]
    fn is_attacked(&self, target: u8, by: i8) -> bool {
        is_attacked_on(&self.board, target, by)
    }

    #[inline(always)]
    fn in_check(&self, side: i8) -> bool {
        self.is_attacked(self.king_of(side), -side)
    }

    fn ep_hash_file(&self) -> Option<usize> {
        if self.ep < 0 {
            return None;
        }
        let target = self.ep as u8;
        let cap_sq = (target as i16 - self.side as i16 * 8) as u8;
        for df in [-1, 1] {
            let Some(from) = square(file(target) + df, rank(target) - self.side) else {
                continue;
            };
            if self.board[from as usize] != self.side * PAWN {
                continue;
            }
            let mut test = self.clone();
            test.board[from as usize] = EMPTY;
            test.board[cap_sq as usize] = EMPTY;
            test.board[target as usize] = self.side * PAWN;
            if !test.is_attacked(test.king_of(self.side), -self.side) {
                return Some(file(target) as usize);
            }
        }
        None
    }

    fn make_move(&mut self, mv: u32) -> Undo {
        let from = move_from(mv);
        let to = move_to(mv);
        let piece = self.board[from as usize];
        let undo = Undo {
            captured: if mv & FLAG_EP != 0 {
                -self.side * PAWN
            } else {
                self.board[to as usize]
            },
            castle: self.castle,
            ep: self.ep,
            halfmove: self.halfmove,
            fullmove: self.fullmove,
            hash: self.hash,
            mg: self.mg,
            eg: self.eg,
            phase: self.phase,
            king_sq: self.king_sq,
        };
        self.hash ^= zobrist().castle[self.castle as usize];
        if let Some(ep_file) = self.ep_hash_file() {
            self.hash ^= zobrist().ep[ep_file];
        }
        self.ep = -1;
        self.halfmove = self.halfmove.saturating_add(1);
        self.remove_piece(from);
        if mv & FLAG_EP != 0 {
            let cap_sq = (to as i16 - self.side as i16 * 8) as u8;
            self.remove_piece(cap_sq);
        } else if self.board[to as usize] != EMPTY {
            self.remove_piece(to);
        }
        let placed = if mv & FLAG_PROMO != 0 {
            self.side * move_promo(mv)
        } else {
            piece
        };
        self.add_piece(to, placed);
        if kind(piece) == KING {
            self.king_sq[if self.side == WHITE { 0 } else { 1 }] = to;
            if self.side == WHITE {
                self.castle &= !3;
            } else {
                self.castle &= !12;
            }
            if mv & FLAG_CASTLE != 0 {
                let (rf, rt) = if to > from {
                    (from + 3, from + 1)
                } else {
                    (from - 4, from - 1)
                };
                let rook = self.remove_piece(rf);
                self.add_piece(rt, rook);
            }
        }
        if kind(piece) == ROOK {
            match from {
                0 => self.castle &= !2,
                7 => self.castle &= !1,
                56 => self.castle &= !8,
                63 => self.castle &= !4,
                _ => {}
            }
        }
        if undo.captured.abs() == ROOK {
            match to {
                0 => self.castle &= !2,
                7 => self.castle &= !1,
                56 => self.castle &= !8,
                63 => self.castle &= !4,
                _ => {}
            }
        }
        if kind(piece) == PAWN || undo.captured != EMPTY {
            self.halfmove = 0;
        }
        if mv & FLAG_DOUBLE != 0 {
            self.ep = (from as i16 + self.side as i16 * 8) as i8;
        }
        if self.side == BLACK {
            self.fullmove = self.fullmove.saturating_add(1);
        }
        self.hash ^= zobrist().castle[self.castle as usize];
        self.side = -self.side;
        self.hash ^= zobrist().side;
        if let Some(ep_file) = self.ep_hash_file() {
            self.hash ^= zobrist().ep[ep_file];
        }
        undo
    }

    fn unmake_move(&mut self, mv: u32, undo: Undo) {
        self.side = -self.side;
        let from = move_from(mv);
        let to = move_to(mv);
        let moved = self.board[to as usize];
        self.board[from as usize] = if mv & FLAG_PROMO != 0 {
            self.side * PAWN
        } else {
            moved
        };
        self.board[to as usize] = EMPTY;
        if mv & FLAG_CASTLE != 0 {
            let (rf, rt) = if to > from {
                (from + 3, from + 1)
            } else {
                (from - 4, from - 1)
            };
            self.board[rf as usize] = self.board[rt as usize];
            self.board[rt as usize] = EMPTY;
        }
        if mv & FLAG_EP != 0 {
            let cap_sq = (to as i16 - self.side as i16 * 8) as u8;
            self.board[cap_sq as usize] = undo.captured;
        } else {
            self.board[to as usize] = undo.captured;
        }
        self.castle = undo.castle;
        self.ep = undo.ep;
        self.halfmove = undo.halfmove;
        self.fullmove = undo.fullmove;
        self.hash = undo.hash;
        self.mg = undo.mg;
        self.eg = undo.eg;
        self.phase = undo.phase;
        self.king_sq = undo.king_sq;
    }
}

#[inline(always)]
fn is_attacked_on(board: &[i8; 64], target: u8, by: i8) -> bool {
    let tf = file(target);
    let tr = rank(target);
    let pawn_rank = tr - by;
    for df in [-1, 1] {
        if let Some(sq) = square(tf + df, pawn_rank) {
            if board[sq as usize] == by * PAWN {
                return true;
            }
        }
    }
    for &(df, dr) in &KNIGHT_DELTAS {
        if let Some(sq) = square(tf + df, tr + dr) {
            if board[sq as usize] == by * KNIGHT {
                return true;
            }
        }
    }
    for &(df, dr) in &KING_DELTAS {
        if let Some(sq) = square(tf + df, tr + dr) {
            if board[sq as usize] == by * KING {
                return true;
            }
        }
    }
    for &(df, dr) in &BISHOP_DIRS {
        let mut f = tf + df;
        let mut r = tr + dr;
        while let Some(sq) = square(f, r) {
            let p = board[sq as usize];
            if p != EMPTY {
                if p == by * BISHOP || p == by * QUEEN {
                    return true;
                }
                break;
            }
            f += df;
            r += dr;
        }
    }
    for &(df, dr) in &ROOK_DIRS {
        let mut f = tf + df;
        let mut r = tr + dr;
        while let Some(sq) = square(f, r) {
            let p = board[sq as usize];
            if p != EMPTY {
                if p == by * ROOK || p == by * QUEEN {
                    return true;
                }
                break;
            }
            f += df;
            r += dr;
        }
    }
    false
}

#[derive(Clone)]
struct MoveList {
    moves: [u32; MAX_MOVES],
    scores: [i32; MAX_MOVES],
    see_scores: [i16; MAX_MOVES],
    len: usize,
}
impl MoveList {
    #[inline(always)]
    fn new() -> Self {
        Self {
            moves: [0; MAX_MOVES],
            scores: [0; MAX_MOVES],
            see_scores: [0; MAX_MOVES],
            len: 0,
        }
    }
    #[inline(always)]
    fn push(&mut self, mv: u32) {
        self.moves[self.len] = mv;
        self.len += 1;
    }
    #[inline(always)]
    fn pick(&mut self, index: usize) -> u32 {
        let mut best = index;
        for i in index + 1..self.len {
            if self.scores[i] > self.scores[best] {
                best = i;
            }
        }
        self.moves.swap(index, best);
        self.scores.swap(index, best);
        self.see_scores.swap(index, best);
        self.moves[index]
    }
}

fn generate_pseudo(pos: &Position, list: &mut MoveList, tactical_only: bool) {
    list.len = 0;
    let side = pos.side;
    for from in 0..64u8 {
        let piece = pos.board[from as usize];
        if color(piece) != side {
            continue;
        }
        let ff = file(from);
        let fr = rank(from);
        match kind(piece) {
            PAWN => {
                let promotion_rank = if side == WHITE { 7 } else { 0 };
                let start_rank = if side == WHITE { 1 } else { 6 };
                if let Some(to) = square(ff, fr + side) {
                    if pos.board[to as usize] == EMPTY {
                        if rank(to) == promotion_rank {
                            for promo in [QUEEN, ROOK, BISHOP, KNIGHT] {
                                list.push(encode_move(from, to, promo, FLAG_PROMO));
                            }
                        } else if !tactical_only {
                            list.push(encode_move(from, to, 0, 0));
                            if fr == start_rank {
                                let to2 = square(ff, fr + 2 * side).unwrap();
                                if pos.board[to2 as usize] == EMPTY {
                                    list.push(encode_move(from, to2, 0, FLAG_DOUBLE));
                                }
                            }
                        }
                    }
                }
                for df in [-1, 1] {
                    if let Some(to) = square(ff + df, fr + side) {
                        let target = pos.board[to as usize];
                        if color(target) == -side && kind(target) != KING {
                            if rank(to) == promotion_rank {
                                for promo in [QUEEN, ROOK, BISHOP, KNIGHT] {
                                    list.push(encode_move(
                                        from,
                                        to,
                                        promo,
                                        FLAG_CAPTURE | FLAG_PROMO,
                                    ));
                                }
                            } else {
                                list.push(encode_move(from, to, 0, FLAG_CAPTURE));
                            }
                        } else if pos.ep == to as i8
                            && target == EMPTY
                            && pos.board[(to as i16 - side as i16 * 8) as usize] == -side * PAWN
                        {
                            list.push(encode_move(from, to, 0, FLAG_CAPTURE | FLAG_EP));
                        }
                    }
                }
            }
            KNIGHT => {
                for &(df, dr) in &KNIGHT_DELTAS {
                    if let Some(to) = square(ff + df, fr + dr) {
                        let target = pos.board[to as usize];
                        if color(target) == -side && kind(target) != KING {
                            list.push(encode_move(from, to, 0, FLAG_CAPTURE));
                        } else if target == EMPTY && !tactical_only {
                            list.push(encode_move(from, to, 0, 0));
                        }
                    }
                }
            }
            BISHOP | ROOK | QUEEN => {
                let dirs: &[(i8, i8)] = if kind(piece) == BISHOP {
                    &BISHOP_DIRS
                } else if kind(piece) == ROOK {
                    &ROOK_DIRS
                } else {
                    &KING_DELTAS
                };
                for &(df, dr) in dirs {
                    let mut f = ff + df;
                    let mut r = fr + dr;
                    while let Some(to) = square(f, r) {
                        let target = pos.board[to as usize];
                        if target == EMPTY {
                            if !tactical_only {
                                list.push(encode_move(from, to, 0, 0));
                            }
                        } else {
                            if color(target) == -side && kind(target) != KING {
                                list.push(encode_move(from, to, 0, FLAG_CAPTURE));
                            }
                            break;
                        }
                        f += df;
                        r += dr;
                    }
                }
            }
            KING => {
                for &(df, dr) in &KING_DELTAS {
                    if let Some(to) = square(ff + df, fr + dr) {
                        let target = pos.board[to as usize];
                        if color(target) == -side && kind(target) != KING {
                            list.push(encode_move(from, to, 0, FLAG_CAPTURE));
                        } else if target == EMPTY && !tactical_only {
                            list.push(encode_move(from, to, 0, 0));
                        }
                    }
                }
                let side_rights = if side == WHITE { 3 } else { 12 };
                if !tactical_only && pos.castle & side_rights != 0 && !pos.in_check(side) {
                    if side == WHITE && from == 4 {
                        if pos.castle & 1 != 0
                            && pos.board[5] == 0
                            && pos.board[6] == 0
                            && pos.board[7] == ROOK
                            && !pos.is_attacked(5, BLACK)
                            && !pos.is_attacked(6, BLACK)
                        {
                            list.push(encode_move(4, 6, 0, FLAG_CASTLE));
                        }
                        if pos.castle & 2 != 0
                            && pos.board[3] == 0
                            && pos.board[2] == 0
                            && pos.board[1] == 0
                            && pos.board[0] == ROOK
                            && !pos.is_attacked(3, BLACK)
                            && !pos.is_attacked(2, BLACK)
                        {
                            list.push(encode_move(4, 2, 0, FLAG_CASTLE));
                        }
                    } else if side == BLACK && from == 60 {
                        if pos.castle & 4 != 0
                            && pos.board[61] == 0
                            && pos.board[62] == 0
                            && pos.board[63] == -ROOK
                            && !pos.is_attacked(61, WHITE)
                            && !pos.is_attacked(62, WHITE)
                        {
                            list.push(encode_move(60, 62, 0, FLAG_CASTLE));
                        }
                        if pos.castle & 8 != 0
                            && pos.board[59] == 0
                            && pos.board[58] == 0
                            && pos.board[57] == 0
                            && pos.board[56] == -ROOK
                            && !pos.is_attacked(59, WHITE)
                            && !pos.is_attacked(58, WHITE)
                        {
                            list.push(encode_move(60, 58, 0, FLAG_CASTLE));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

#[inline(always)]
fn move_keeps_king_safe(pos: &mut Position, mv: u32, side: i8) -> bool {
    let from = move_from(mv);
    let to = move_to(mv);
    let moving = pos.board[from as usize];
    let captured = pos.board[to as usize];
    let old_king = pos.king_of(side);
    let cap_sq = if mv & FLAG_EP != 0 {
        Some((to as i16 - side as i16 * 8) as u8)
    } else {
        None
    };
    pos.board[from as usize] = EMPTY;
    if let Some(sq) = cap_sq {
        pos.board[sq as usize] = EMPTY;
    }
    pos.board[to as usize] = if mv & FLAG_PROMO != 0 {
        side * move_promo(mv)
    } else {
        moving
    };
    let king = if kind(moving) == KING { to } else { old_king };
    let legal = !pos.is_attacked(king, -side);
    pos.board[from as usize] = moving;
    pos.board[to as usize] = captured;
    if let Some(sq) = cap_sq {
        pos.board[sq as usize] = -side * PAWN;
    }
    legal
}

fn generate_legal(pos: &mut Position, list: &mut MoveList, tactical_only: bool) {
    let side = pos.side;
    generate_pseudo(pos, list, tactical_only);
    let mut out = 0;
    for i in 0..list.len {
        let mv = list.moves[i];
        if move_keeps_king_safe(pos, mv, side) {
            list.moves[out] = mv;
            out += 1;
        }
    }
    list.len = out;
}

fn has_legal_move(pos: &mut Position) -> bool {
    let side = pos.side;
    // Most quiet leaves have an immediately legal pawn or knight move. Probe these
    // directly before paying to materialize every pseudo-legal move.
    for from in 0..64u8 {
        let piece = pos.board[from as usize];
        if piece == side * PAWN {
            let ff = file(from);
            let fr = rank(from);
            if let Some(to) = square(ff, fr + side) {
                if pos.board[to as usize] == EMPTY {
                    let promo = if rank(to) == if side == WHITE { 7 } else { 0 } {
                        FLAG_PROMO
                    } else {
                        0
                    };
                    let mv = encode_move(from, to, QUEEN, promo);
                    if move_keeps_king_safe(pos, mv, side) {
                        return true;
                    }
                    let start_rank = if side == WHITE { 1 } else { 6 };
                    if fr == start_rank {
                        let to2 = square(ff, fr + 2 * side).unwrap();
                        if pos.board[to2 as usize] == EMPTY {
                            let mv = encode_move(from, to2, 0, FLAG_DOUBLE);
                            if move_keeps_king_safe(pos, mv, side) {
                                return true;
                            }
                        }
                    }
                }
            }
            for df in [-1, 1] {
                if let Some(to) = square(ff + df, fr + side) {
                    let target = pos.board[to as usize];
                    let flags = if color(target) == -side && kind(target) != KING {
                        FLAG_CAPTURE
                            | if rank(to) == if side == WHITE { 7 } else { 0 } {
                                FLAG_PROMO
                            } else {
                                0
                            }
                    } else if pos.ep == to as i8
                        && target == EMPTY
                        && pos.board[(to as i16 - side as i16 * 8) as usize] == -side * PAWN
                    {
                        FLAG_CAPTURE | FLAG_EP
                    } else {
                        continue;
                    };
                    let mv = encode_move(from, to, QUEEN, flags);
                    if move_keeps_king_safe(pos, mv, side) {
                        return true;
                    }
                }
            }
        } else if piece == side * KNIGHT {
            for &(df, dr) in &KNIGHT_DELTAS {
                let Some(to) = square(file(from) + df, rank(from) + dr) else {
                    continue;
                };
                let target = pos.board[to as usize];
                if color(target) == side || kind(target) == KING {
                    continue;
                }
                let mv = encode_move(from, to, 0, if target == EMPTY { 0 } else { FLAG_CAPTURE });
                if move_keeps_king_safe(pos, mv, side) {
                    return true;
                }
            }
        }
    }
    let mut list = MoveList::new();
    generate_pseudo(pos, &mut list, false);
    for i in 0..list.len {
        let mv = list.moves[i];
        if move_keeps_king_safe(pos, mv, side) {
            return true;
        }
    }
    false
}

fn parse_square(s: &str) -> Option<u8> {
    let b = s.as_bytes();
    if b.len() != 2 || !(b'a'..=b'h').contains(&b[0]) || !(b'1'..=b'8').contains(&b[1]) {
        return None;
    }
    Some((b[1] - b'1') * 8 + b[0] - b'a')
}

fn square_name(sq: u8) -> String {
    let mut result = String::with_capacity(2);
    result.push((b'a' + sq % 8) as char);
    result.push((b'1' + sq / 8) as char);
    result
}

fn move_to_uci(mv: u32) -> String {
    let mut s = String::with_capacity(5);
    for sq in [move_from(mv), move_to(mv)] {
        s.push_str(&square_name(sq));
    }
    if mv & FLAG_PROMO != 0 {
        s.push(match move_promo(mv) {
            KNIGHT => 'n',
            BISHOP => 'b',
            ROOK => 'r',
            _ => 'q',
        });
    }
    s
}

fn parse_uci_move(pos: &mut Position, text: &str) -> Option<u32> {
    let bytes = text.as_bytes();
    if !text.is_ascii() || !matches!(bytes.len(), 4 | 5) {
        return None;
    }
    let from = parse_square(&text[..2])?;
    let to = parse_square(&text[2..4])?;
    let promotion = if bytes.len() == 5 {
        match bytes[4] {
            b'q' => QUEEN,
            b'r' => ROOK,
            b'b' => BISHOP,
            b'n' => KNIGHT,
            _ => return None,
        }
    } else {
        0
    };
    let mut list = MoveList::new();
    generate_legal(pos, &mut list, false);
    (0..list.len).map(|i| list.moves[i]).find(|&mv| {
        move_from(mv) == from
            && move_to(mv) == to
            && if mv & FLAG_PROMO != 0 {
                promotion == move_promo(mv)
            } else {
                promotion == 0
            }
    })
}

const OPENING_BOOK: [(&str, &str); 13] = [
    ("", "e2e4"),
    ("e2e4", "c7c5"),
    ("e2e4 c7c5", "g1f3"),
    ("e2e4 c7c5 g1f3", "d7d6"),
    ("e2e4 c7c5 g1f3 d7d6", "d2d4"),
    ("e2e4 c7c5 g1f3 d7d6 d2d4", "c5d4"),
    ("e2e4 c7c5 g1f3 d7d6 d2d4 c5d4", "f3d4"),
    ("e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4", "g8f6"),
    ("e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6", "b1c3"),
    ("d2d4", "g8f6"),
    ("d2d4 g8f6 c2c4", "e7e6"),
    ("d2d4 g8f6 c2c4 e7e6 b1c3", "f8b4"),
    ("g1f3", "d7d5"),
];

fn opening_move(pos: &mut Position) -> Option<u32> {
    if pos.fullmove > 5 {
        return None;
    }
    for (line, choice) in OPENING_BOOK {
        let mut expected = Position::from_fen(START_FEN).ok()?;
        let mut valid = true;
        for text in line.split_whitespace() {
            let Some(mv) = parse_uci_move(&mut expected, text) else {
                valid = false;
                break;
            };
            expected.make_move(mv);
        }
        if valid && expected.hash == pos.hash {
            return parse_uci_move(pos, choice);
        }
    }
    None
}

fn piece_eval(piece: i8, sq: u8) -> (i32, i32, i32) {
    let side = color(piece);
    let k = kind(piece) as usize;
    let r = if side == WHITE {
        rank(sq)
    } else {
        7 - rank(sq)
    } as i32;
    let f = file(sq) as i32;
    let file_center = (f - 3).abs().min((f - 4).abs());
    let rank_center = (r - 3).abs().min((r - 4).abs());
    let center = 6 - file_center - rank_center;
    let (mg_pos, eg_pos) = match kind(piece) {
        PAWN => (r * 7 - file_center * 2, r * 12),
        KNIGHT => (center * 9, center * 6),
        BISHOP => (center * 5, center * 5),
        ROOK => (r * 2, center * 2),
        QUEEN => (center * 2, center * 4),
        KING => (-center * 10 - r * 3, center * 10),
        _ => (0, 0),
    };
    let phase = match kind(piece) {
        KNIGHT | BISHOP => 1,
        ROOK => 2,
        QUEEN => 4,
        _ => 0,
    };
    (
        side as i32 * (PIECE_VALUE[k] + mg_pos),
        side as i32 * (PIECE_VALUE[k] + eg_pos),
        phase,
    )
}

fn perft(pos: &mut Position, depth: u32) -> u64 {
    if depth == 0 {
        return 1;
    }
    let mut list = MoveList::new();
    generate_legal(pos, &mut list, false);
    if depth == 1 {
        return list.len as u64;
    }
    let mut nodes = 0;
    for i in 0..list.len {
        let mv = list.moves[i];
        let undo = pos.make_move(mv);
        nodes += perft(pos, depth - 1);
        pos.unmake_move(mv, undo);
    }
    nodes
}

// Search and protocol are implemented below.

#[derive(Clone, Copy, Default)]
struct TTEntry {
    key: u64,
    best: u32,
    score: i16,
    depth: i8,
    flag: u8,
    age: u8,
    rule50: u8,
}
const TT_EXACT: u8 = 1;
const TT_LOWER: u8 = 2;
const TT_UPPER: u8 = 3;

struct TransTable {
    entries: Vec<TTEntry>,
    mask: usize,
    age: u8,
}
impl TransTable {
    fn new(mb: usize) -> Self {
        let bytes = mb.max(1) * 1024 * 1024;
        let requested = bytes / std::mem::size_of::<TTEntry>();
        let count = 1usize << (usize::BITS - 1 - requested.leading_zeros());
        Self {
            entries: vec![TTEntry::default(); count],
            mask: count - 1,
            age: 0,
        }
    }
    #[inline(always)]
    fn get(&self, key: u64) -> TTEntry {
        self.entries[key as usize & self.mask]
    }
    #[inline(always)]
    fn put(
        &mut self,
        key: u64,
        depth: i32,
        score: i32,
        flag: u8,
        best: u32,
        ply: usize,
        halfmove: u16,
    ) {
        let idx = key as usize & self.mask;
        let old = self.entries[idx];
        if old.key != key || depth >= old.depth as i32 - 2 || old.age != self.age {
            let stored = if score > MATE - MAX_PLY as i32 {
                score + ply as i32
            } else if score < -MATE + MAX_PLY as i32 {
                score - ply as i32
            } else {
                score
            };
            self.entries[idx] = TTEntry {
                key,
                best,
                score: stored.clamp(-32767, 32767) as i16,
                depth: depth.clamp(-1, 127) as i8,
                flag,
                age: self.age,
                rule50: halfmove.min(100) as u8,
            };
        }
    }
}

#[derive(Clone, Copy)]
struct NullUndo {
    ep: i8,
    halfmove: u16,
    hash: u64,
}
impl Position {
    #[inline(always)]
    fn make_null(&mut self) -> NullUndo {
        let undo = NullUndo {
            ep: self.ep,
            halfmove: self.halfmove,
            hash: self.hash,
        };
        if let Some(ep_file) = self.ep_hash_file() {
            self.hash ^= zobrist().ep[ep_file];
        }
        self.ep = -1;
        self.halfmove = self.halfmove.saturating_add(1);
        self.side = -self.side;
        self.hash ^= zobrist().side;
        undo
    }
    #[inline(always)]
    fn unmake_null(&mut self, undo: NullUndo) {
        self.side = -self.side;
        self.ep = undo.ep;
        self.halfmove = undo.halfmove;
        self.hash = undo.hash;
    }
}

fn evaluate(pos: &Position) -> i32 {
    let phase = pos.phase.min(24);
    let mut score = (pos.mg * phase + pos.eg * (24 - phase)) / 24;
    let mut bishops = [0; 2];
    let mut pawns_by_file = [[0u8; 8]; 2];
    let mut pawn_squares = [[0u8; 8]; 2];
    let mut pawn_count = [0usize; 2];
    let mut rook_squares = [[0u8; 10]; 2];
    let mut rook_count = [0usize; 2];
    let mut queens = [0i32; 2];
    for sq in 0..64u8 {
        let p = pos.board[sq as usize];
        if p == 0 {
            continue;
        }
        let ci = if p > 0 { 0 } else { 1 };
        let side = color(p);
        if kind(p) == BISHOP {
            bishops[ci] += 1;
        }
        if kind(p) == ROOK && rook_count[ci] < rook_squares[ci].len() {
            rook_squares[ci][rook_count[ci]] = sq;
            rook_count[ci] += 1;
        }
        if kind(p) == QUEEN {
            queens[ci] += 1;
        }
        if kind(p) == PAWN {
            pawns_by_file[ci][file(sq) as usize] += 1;
            if pawn_count[ci] < 8 {
                pawn_squares[ci][pawn_count[ci]] = sq;
                pawn_count[ci] += 1;
            }
        }
        let mobility_weight = match kind(p) {
            KNIGHT => 4,
            BISHOP => 4,
            ROOK => 2,
            QUEEN => 1,
            _ => 0,
        };
        if mobility_weight != 0 {
            let sf = file(sq);
            let sr = rank(sq);
            let mut mobility = 0;
            if kind(p) == KNIGHT {
                for &(df, dr) in &KNIGHT_DELTAS {
                    if let Some(to) = square(sf + df, sr + dr) {
                        if color(pos.board[to as usize]) != side {
                            mobility += 1;
                        }
                    }
                }
            } else {
                let dirs: &[(i8, i8)] = if kind(p) == BISHOP {
                    &BISHOP_DIRS
                } else if kind(p) == ROOK {
                    &ROOK_DIRS
                } else {
                    &KING_DELTAS
                };
                for &(df, dr) in dirs {
                    let mut f = sf + df;
                    let mut r = sr + dr;
                    while let Some(to) = square(f, r) {
                        if color(pos.board[to as usize]) == side {
                            break;
                        }
                        mobility += 1;
                        if pos.board[to as usize] != EMPTY {
                            break;
                        }
                        f += df;
                        r += dr;
                    }
                }
            }
            score += side as i32 * mobility * mobility_weight;
        }
    }
    if bishops[0] >= 2 {
        score += 28;
    }
    if bishops[1] >= 2 {
        score -= 28;
    }
    for side_idx in 0..2 {
        let side = if side_idx == 0 { WHITE } else { BLACK };
        let sign = side as i32;
        for f in 0..8 {
            if pawns_by_file[side_idx][f] > 1 {
                score -= sign * 12 * (pawns_by_file[side_idx][f] as i32 - 1);
            }
        }
        for i in 0..pawn_count[side_idx] {
            let sq = pawn_squares[side_idx][i];
            let f = file(sq) as usize;
            let isolated = (f == 0 || pawns_by_file[side_idx][f - 1] == 0)
                && (f == 7 || pawns_by_file[side_idx][f + 1] == 0);
            if isolated {
                score -= sign * 10;
            }
            let mut passed = true;
            for j in 0..pawn_count[1 - side_idx] {
                let enemy = pawn_squares[1 - side_idx][j];
                if (file(enemy) - file(sq)).abs() <= 1 && (rank(enemy) - rank(sq)) * side > 0 {
                    passed = false;
                    break;
                }
            }
            if passed {
                let advance = if side == WHITE {
                    rank(sq)
                } else {
                    7 - rank(sq)
                } as i32;
                let frontmost = !(0..pawn_count[side_idx]).any(|j| {
                    file(pawn_squares[side_idx][j]) == file(sq)
                        && (rank(pawn_squares[side_idx][j]) - rank(sq)) * side > 0
                });
                if frontmost {
                    let mut bonus = (12 + advance * advance * 4) * (32 - phase) / 24;
                    for df in [-1, 1] {
                        if let Some(defender) = square(file(sq) + df, rank(sq) - side) {
                            if pos.board[defender as usize] == side * PAWN {
                                bonus += 12;
                            }
                        }
                    }
                    score += sign * bonus;
                }
            }
        }
        // Rooks benefit from files where their own pawn is absent, especially fully open files.
        for &sq in &rook_squares[side_idx][..rook_count[side_idx]] {
            let f = file(sq) as usize;
            if pawns_by_file[side_idx][f] == 0 {
                score += sign
                    * if pawns_by_file[1 - side_idx][f] == 0 {
                        18
                    } else {
                        10
                    };
            }
            let relative_rank = if side == WHITE {
                rank(sq)
            } else {
                7 - rank(sq)
            };
            if relative_rank == 6 {
                score += sign * 18;
            }
        }
        if phase > 0 {
            let king = pos.king_of(side);
            let kr = rank(king);
            let kf = file(king);
            let shield_rank = kr + side;
            let mut shield = 0;
            for df in -1..=1 {
                if let Some(sq) = square(kf + df, shield_rank) {
                    if pos.board[sq as usize] == side * PAWN {
                        shield += 1;
                    }
                }
            }
            let mut exposure = 0;
            for df in -1..=1 {
                let f = kf + df;
                if (0..8).contains(&f) && pawns_by_file[side_idx][f as usize] == 0 {
                    exposure += if pawns_by_file[1 - side_idx][f as usize] == 0 {
                        8
                    } else {
                        4
                    };
                }
            }
            let enemy_heavy = queens[1 - side_idx] * 2 + rook_count[1 - side_idx] as i32;
            score += sign * (shield * 12 - exposure * enemy_heavy) * phase / 24;
        }
    }
    (score + if pos.side == WHITE { 8 } else { -8 }) * pos.side as i32
}

#[inline]
fn insufficient_material(pos: &Position) -> bool {
    let mut knights = [0; 2];
    let mut bishops = [0; 2];
    let mut bishop_color = None;
    for sq in 0..64u8 {
        let piece = pos.board[sq as usize];
        match kind(piece) {
            PAWN | ROOK | QUEEN => return false,
            KNIGHT => knights[if piece > 0 { 0 } else { 1 }] += 1,
            BISHOP => {
                bishops[if piece > 0 { 0 } else { 1 }] += 1;
                let color = (file(sq) + rank(sq)) & 1;
                if bishop_color.is_some_and(|old| old != color) {
                    bishop_color = Some(2);
                } else if bishop_color.is_none() {
                    bishop_color = Some(color);
                }
            }
            _ => {}
        }
    }
    let total_knights = knights[0] + knights[1];
    let total_bishops = bishops[0] + bishops[1];
    total_knights + total_bishops <= 1 || (total_knights == 0 && bishop_color != Some(2))
}

#[inline]
fn has_non_pawn_material(pos: &Position, side: i8) -> bool {
    pos.board
        .iter()
        .any(|&piece| color(piece) == side && matches!(kind(piece), KNIGHT | BISHOP | ROOK | QUEEN))
}

fn piece_attacks_square(board: &[i8; 64], from: u8, target: u8, piece: i8) -> bool {
    let df = file(target) - file(from);
    let dr = rank(target) - rank(from);
    let attacks = match kind(piece) {
        PAWN => dr == color(piece) && df.abs() == 1,
        KNIGHT => matches!((df.abs(), dr.abs()), (1, 2) | (2, 1)),
        BISHOP => df.abs() == dr.abs(),
        ROOK => df == 0 || dr == 0,
        QUEEN => df == 0 || dr == 0 || df.abs() == dr.abs(),
        KING => df.abs().max(dr.abs()) == 1,
        _ => false,
    };
    if !attacks || !matches!(kind(piece), BISHOP | ROOK | QUEEN) {
        return attacks;
    }
    let step_file = df.signum();
    let step_rank = dr.signum();
    let mut f = file(from) + step_file;
    let mut r = rank(from) + step_rank;
    while let Some(sq) = square(f, r) {
        if sq == target {
            return true;
        }
        if board[sq as usize] != EMPTY {
            return false;
        }
        f += step_file;
        r += step_rank;
    }
    false
}

fn least_legal_attacker(
    board: &[i8; 64],
    target: u8,
    side: i8,
    king_sq: [u8; 2],
) -> Option<(u8, i8)> {
    let side_index = if side == WHITE { 0 } else { 1 };
    let mut best = None;
    let mut best_value = i32::MAX;
    for sq in 0..64u8 {
        let piece = board[sq as usize];
        if color(piece) != side || !piece_attacks_square(board, sq, target, piece) {
            continue;
        }
        let attacker = kind(piece);
        let value = PIECE_VALUE[attacker as usize];
        if value >= best_value {
            continue;
        }
        let placed = if attacker == PAWN && matches!(rank(target), 0 | 7) {
            QUEEN
        } else {
            attacker
        };
        let mut test = *board;
        test[sq as usize] = EMPTY;
        test[target as usize] = side * placed;
        let king = if attacker == KING {
            target
        } else {
            king_sq[side_index]
        };
        if !is_attacked_on(&test, king, -side) {
            best = Some((sq, attacker));
            best_value = value;
        }
    }
    best
}

fn see(pos: &Position, mv: u32) -> i32 {
    if mv & FLAG_CAPTURE == 0 {
        return 0;
    }
    let from = move_from(mv);
    let to = move_to(mv);
    let captured = if mv & FLAG_EP != 0 {
        PAWN
    } else {
        kind(pos.board[to as usize])
    };
    let mut board = pos.board;
    board[from as usize] = 0;
    if mv & FLAG_EP != 0 {
        board[(to as i16 - pos.side as i16 * 8) as usize] = 0;
    }
    let placed = if mv & FLAG_PROMO != 0 {
        move_promo(mv)
    } else {
        kind(pos.board[from as usize])
    };
    board[to as usize] = pos.side * placed;
    let mut king_sq = pos.king_sq;
    if placed == KING {
        king_sq[if pos.side == WHITE { 0 } else { 1 }] = to;
    }
    let mut gain = [0i32; 32];
    gain[0] = PIECE_VALUE[captured as usize]
        + if mv & FLAG_PROMO != 0 {
            PIECE_VALUE[placed as usize] - PIECE_VALUE[PAWN as usize]
        } else {
            0
        };
    let mut side = -pos.side;
    let mut victim = placed;
    let mut depth = 0usize;
    while depth < 30 {
        let Some((sq, attacker)) = least_legal_attacker(&board, to, side, king_sq) else {
            break;
        };
        depth += 1;
        let promotes = attacker == PAWN && matches!(rank(to), 0 | 7);
        gain[depth] = PIECE_VALUE[victim as usize] - gain[depth - 1]
            + if promotes {
                PIECE_VALUE[QUEEN as usize] - PIECE_VALUE[PAWN as usize]
            } else {
                0
            };
        board[sq as usize] = 0;
        let placed_attacker = if promotes { QUEEN } else { attacker };
        board[to as usize] = side * placed_attacker;
        let side_index = if side == WHITE { 0 } else { 1 };
        if attacker == KING {
            king_sq[side_index] = to;
        }
        victim = placed_attacker;
        side = -side;
        if attacker == KING {
            break;
        }
    }
    while depth > 0 {
        depth -= 1;
        gain[depth] = -(-gain[depth]).max(gain[depth + 1]);
    }
    gain[0]
}

struct Searcher {
    tt: TransTable,
    own_book: bool,
    silent: bool,
    stop: Arc<AtomicBool>,
    started: Instant,
    soft_limit: Option<Duration>,
    hard_limit: Option<Duration>,
    node_limit: Option<u64>,
    nodes: u64,
    qnodes: u64,
    seldepth: usize,
    stopped: bool,
    killers: [[u32; 2]; MAX_PLY],
    history: [[i32; 64]; 12],
    counter: [u32; 4096],
    hashes: [u64; 512],
    hash_len: usize,
    null_depth: u8,
}

impl Searcher {
    fn new(hash_mb: usize, stop: Arc<AtomicBool>) -> Self {
        Self {
            tt: TransTable::new(hash_mb),
            own_book: true,
            silent: false,
            stop,
            started: Instant::now(),
            soft_limit: None,
            hard_limit: None,
            node_limit: None,
            nodes: 0,
            qnodes: 0,
            seldepth: 0,
            stopped: false,
            killers: [[0; 2]; MAX_PLY],
            history: [[0; 64]; 12],
            counter: [0; 4096],
            hashes: [0; 512],
            hash_len: 0,
            null_depth: 0,
        }
    }
    #[inline(always)]
    fn time_check(&mut self) {
        if self.node_limit.is_some_and(|limit| self.nodes >= limit) {
            self.stopped = true;
            return;
        }
        if self.nodes & 63 == 0 {
            self.poll_limits();
        }
    }
    #[inline(always)]
    fn poll_limits(&mut self) {
        if self.stop.load(Ordering::Relaxed)
            || self.node_limit.is_some_and(|limit| self.nodes >= limit)
            || self
                .hard_limit
                .is_some_and(|limit| self.started.elapsed() >= limit)
        {
            self.stopped = true;
        }
    }
    #[inline(always)]
    fn repetition(&self, pos: &Position) -> bool {
        if self.null_depth > 0 || self.hash_len < 3 {
            return false;
        }
        let start = (self.hash_len - 1).saturating_sub(pos.halfmove as usize);
        let mut i = self.hash_len - 3;
        let mut matches = 0;
        while i >= start && i < self.hash_len {
            if self.hashes[i] == pos.hash {
                matches += 1;
                if matches >= 2 {
                    return true;
                }
            }
            if i < 2 {
                break;
            }
            i -= 2;
        }
        false
    }
    #[inline(always)]
    fn push_hash(&mut self, hash: u64) {
        debug_assert!(self.hash_len < self.hashes.len());
        self.hashes[self.hash_len] = hash;
        self.hash_len += 1;
    }
    #[inline(always)]
    fn pop_hash(&mut self) {
        if self.hash_len > 0 {
            self.hash_len -= 1;
        }
    }

    fn order_moves(
        &self,
        pos: &Position,
        list: &mut MoveList,
        tt_move: u32,
        ply: usize,
        prev: u32,
    ) {
        for i in 0..list.len {
            let mv = list.moves[i];
            list.see_scores[i] = 0;
            list.scores[i] = if mv == tt_move {
                2_000_000
            } else if mv & FLAG_PROMO != 0 {
                1_200_000 + PIECE_VALUE[move_promo(mv) as usize]
            } else if mv & FLAG_CAPTURE != 0 {
                let victim = if mv & FLAG_EP != 0 {
                    PAWN
                } else {
                    kind(pos.board[move_to(mv) as usize])
                };
                let exchange = see(pos, mv);
                list.see_scores[i] = exchange.clamp(i16::MIN as i32, i16::MAX as i32) as i16;
                let base = if exchange >= 0 { 1_000_000 } else { 820_000 };
                base + exchange * 32 + PIECE_VALUE[victim as usize]
                    - PIECE_VALUE[kind(pos.board[move_from(mv) as usize]) as usize] / 16
            } else if ply < MAX_PLY && mv == self.killers[ply][0] {
                900_000
            } else if ply < MAX_PLY && mv == self.killers[ply][1] {
                890_000
            } else if prev != 0 && mv == self.counter[(prev & 4095) as usize] {
                880_000
            } else {
                self.history[piece_index(pos.board[move_from(mv) as usize])][move_to(mv) as usize]
            };
        }
    }

    fn quiescence(&mut self, pos: &mut Position, mut alpha: i32, beta: i32, ply: usize) -> i32 {
        self.nodes += 1;
        self.qnodes += 1;
        self.seldepth = self.seldepth.max(ply);
        self.time_check();
        if self.stopped {
            return 0;
        }
        let in_check = pos.in_check(pos.side);
        if pos.halfmove >= 100 {
            if in_check {
                let mut evasions = MoveList::new();
                generate_legal(pos, &mut evasions, false);
                if evasions.len == 0 {
                    return -MATE + ply as i32;
                }
            }
            return 0;
        }
        if self.repetition(pos) || insufficient_material(pos) {
            return 0;
        }
        if ply >= MAX_PLY - 1 {
            return evaluate(pos);
        }
        let mut list = MoveList::new();
        generate_legal(pos, &mut list, !in_check);
        if in_check && list.len == 0 {
            return -MATE + ply as i32;
        }
        if !in_check && list.len == 0 {
            if !has_legal_move(pos) {
                return 0;
            }
        }
        let stand = if in_check { 0 } else { evaluate(pos) };
        if !in_check {
            if stand >= beta {
                return stand;
            }
            if stand > alpha {
                alpha = stand;
            }
        }
        self.order_moves(pos, &mut list, 0, ply, 0);
        for i in 0..list.len {
            let mv = list.pick(i);
            let mut delta_prune = false;
            let mut bad_exchange = false;
            if !in_check && mv & FLAG_CAPTURE != 0 && mv & FLAG_PROMO == 0 {
                let victim = if mv & FLAG_EP != 0 {
                    PAWN
                } else {
                    kind(pos.board[move_to(mv) as usize])
                };
                if stand + PIECE_VALUE[victim as usize] + 180 < alpha && mv & FLAG_PROMO == 0 {
                    delta_prune = true;
                }
                bad_exchange = list.see_scores[i] < -300;
            }
            let undo = pos.make_move(mv);
            let gives_check = pos.in_check(pos.side);
            if !in_check && !gives_check && (delta_prune || bad_exchange) {
                pos.unmake_move(mv, undo);
                continue;
            }
            self.push_hash(pos.hash);
            let score = -self.quiescence(pos, -beta, -alpha, ply + 1);
            self.pop_hash();
            pos.unmake_move(mv, undo);
            if self.stopped {
                return 0;
            }
            if score >= beta {
                return score;
            }
            if score > alpha {
                alpha = score;
            }
        }
        alpha
    }

    fn negamax(
        &mut self,
        pos: &mut Position,
        mut depth: i32,
        mut alpha: i32,
        beta: i32,
        ply: usize,
        pv: bool,
        allow_null: bool,
        prev: u32,
    ) -> i32 {
        self.nodes += 1;
        self.seldepth = self.seldepth.max(ply);
        self.time_check();
        if self.stopped {
            return 0;
        }
        let in_check = pos.in_check(pos.side);
        if pos.halfmove >= 100 {
            if in_check {
                let mut evasions = MoveList::new();
                generate_legal(pos, &mut evasions, false);
                if evasions.len == 0 {
                    return -MATE + ply as i32;
                }
            }
            return 0;
        }
        if (ply > 0 && self.repetition(pos)) || insufficient_material(pos) {
            return 0;
        }
        if ply >= MAX_PLY - 1 {
            return evaluate(pos);
        }
        if in_check {
            depth += 1;
        }
        if depth <= 0 {
            return self.quiescence(pos, alpha, beta, ply);
        }
        let alpha_orig = alpha;
        let entry = self.tt.get(pos.hash);
        let tt_move = if entry.key == pos.hash { entry.best } else { 0 };
        if !pv
            && entry.key == pos.hash
            && (pos.halfmove.saturating_add(depth as u16) < 100
                || entry.rule50 == pos.halfmove.min(100) as u8)
            && entry.depth as i32 >= depth
        {
            let mut score = entry.score as i32;
            if score > MATE - MAX_PLY as i32 {
                score -= ply as i32;
            } else if score < -MATE + MAX_PLY as i32 {
                score += ply as i32;
            }
            if entry.flag == TT_EXACT
                || (entry.flag == TT_LOWER && score >= beta)
                || (entry.flag == TT_UPPER && score <= alpha)
            {
                return score;
            }
        }
        let static_eval = if !pv && !in_check { evaluate(pos) } else { 0 };
        if !pv && !in_check && depth <= 3 && static_eval - 90 * depth >= beta {
            return static_eval;
        }
        if allow_null
            && !pv
            && !in_check
            && depth >= 3
            && static_eval >= beta
            && pos.halfmove < 99
            && has_non_pawn_material(pos, pos.side)
        {
            let undo = pos.make_null();
            let old_hash_len = self.hash_len;
            self.null_depth += 1;
            let reduction = 2 + depth / 5;
            let score = -self.negamax(
                pos,
                depth - 1 - reduction,
                -beta,
                -beta + 1,
                ply + 1,
                false,
                false,
                0,
            );
            self.hash_len = old_hash_len;
            self.null_depth -= 1;
            pos.unmake_null(undo);
            if self.stopped {
                return 0;
            }
            if score >= beta {
                return score;
            }
        }
        let mut list = MoveList::new();
        generate_legal(pos, &mut list, false);
        if list.len == 0 {
            return if in_check { -MATE + ply as i32 } else { 0 };
        }
        self.order_moves(pos, &mut list, tt_move, ply, prev);
        let mut best = -INF;
        let mut best_move = 0;
        let mut searched = 0;
        for i in 0..list.len {
            let mv = list.pick(i);
            let tactical = mv & (FLAG_CAPTURE | FLAG_PROMO) != 0;
            let undo = pos.make_move(mv);
            self.push_hash(pos.hash);
            let gives_check = pos.in_check(pos.side);
            if !pv
                && !in_check
                && depth <= 2
                && !tactical
                && !gives_check
                && searched > 2
                && static_eval + 110 * depth <= alpha
            {
                self.pop_hash();
                pos.unmake_move(mv, undo);
                continue;
            }
            let mut reduction = 0;
            if depth >= 3 && searched >= 3 && !in_check && !tactical && !gives_check {
                reduction = 1;
                if !pv {
                    reduction += (searched / 8).min(2) + (depth / 6).min(1);
                }
            }
            let mut score;
            if searched == 0 {
                score = -self.negamax(pos, depth - 1, -beta, -alpha, ply + 1, pv, true, mv);
            } else {
                score = -self.negamax(
                    pos,
                    depth - 1 - reduction,
                    -alpha - 1,
                    -alpha,
                    ply + 1,
                    false,
                    true,
                    mv,
                );
                if !self.stopped && score > alpha && reduction > 0 {
                    score =
                        -self.negamax(pos, depth - 1, -alpha - 1, -alpha, ply + 1, false, true, mv);
                }
                if !self.stopped && score > alpha && score < beta {
                    score = -self.negamax(pos, depth - 1, -beta, -alpha, ply + 1, true, true, mv);
                }
            }
            self.pop_hash();
            pos.unmake_move(mv, undo);
            searched += 1;
            if self.stopped {
                return 0;
            }
            if score > best {
                best = score;
                best_move = mv;
            }
            if score > alpha {
                alpha = score;
            }
            if alpha >= beta {
                if !tactical && ply < MAX_PLY {
                    if self.killers[ply][0] != mv {
                        self.killers[ply][1] = self.killers[ply][0];
                        self.killers[ply][0] = mv;
                    }
                    let idx = piece_index(pos.board[move_from(mv) as usize]);
                    let bonus = (depth * depth * 16).min(1200);
                    self.history[idx][move_to(mv) as usize] +=
                        bonus - self.history[idx][move_to(mv) as usize] * bonus.abs() / 16_384;
                    for j in 0..i {
                        let failed = list.moves[j];
                        if failed & (FLAG_CAPTURE | FLAG_PROMO) == 0 {
                            let failed_idx = piece_index(pos.board[move_from(failed) as usize]);
                            let entry = &mut self.history[failed_idx][move_to(failed) as usize];
                            *entry += -bonus - *entry * bonus / 16_384;
                        }
                    }
                    if prev != 0 {
                        self.counter[(prev & 4095) as usize] = mv;
                    }
                }
                break;
            }
        }
        if best == -INF {
            best = alpha;
        }
        let flag = if best <= alpha_orig {
            TT_UPPER
        } else if best >= beta {
            TT_LOWER
        } else {
            TT_EXACT
        };
        self.tt
            .put(pos.hash, depth, best, flag, best_move, ply, pos.halfmove);
        best
    }

    fn root_search(
        &mut self,
        pos: &mut Position,
        depth: i32,
        mut alpha: i32,
        beta: i32,
    ) -> (i32, u32) {
        let alpha_orig = alpha;
        let mut list = MoveList::new();
        generate_legal(pos, &mut list, false);
        let entry = self.tt.get(pos.hash);
        let tt_move = if entry.key == pos.hash { entry.best } else { 0 };
        self.order_moves(pos, &mut list, tt_move, 0, 0);
        let mut best = -INF;
        let mut best_move = list.moves[0];
        for i in 0..list.len {
            self.poll_limits();
            if self.stopped {
                break;
            }
            let mv = list.pick(i);
            let undo = pos.make_move(mv);
            self.push_hash(pos.hash);
            let score = if i == 0 {
                -self.negamax(pos, depth - 1, -beta, -alpha, 1, true, true, mv)
            } else {
                let mut s = -self.negamax(pos, depth - 1, -alpha - 1, -alpha, 1, false, true, mv);
                if !self.stopped && s > alpha {
                    s = -self.negamax(pos, depth - 1, -beta, -alpha, 1, true, true, mv);
                }
                s
            };
            self.pop_hash();
            pos.unmake_move(mv, undo);
            if self.stopped {
                break;
            }
            if score > best {
                best = score;
                best_move = mv;
            }
            if score > alpha {
                alpha = score;
            }
            if alpha >= beta {
                break;
            }
        }
        if !self.stopped {
            let flag = if best <= alpha_orig {
                TT_UPPER
            } else if best >= beta {
                TT_LOWER
            } else {
                TT_EXACT
            };
            self.tt
                .put(pos.hash, depth, best, flag, best_move, 0, pos.halfmove);
        }
        (best, best_move)
    }

    fn search(&mut self, pos: &mut Position, limits: GoLimits, game_hashes: &[u64]) -> u32 {
        self.started = Instant::now();
        self.nodes = 0;
        self.qnodes = 0;
        self.seldepth = 0;
        self.stopped = false;
        self.null_depth = 0;
        self.tt.age = self.tt.age.wrapping_add(1);
        self.soft_limit = limits.soft;
        self.hard_limit = limits.hard;
        self.node_limit = limits.nodes;
        self.hash_len = game_hashes.len().min(self.hashes.len() - MAX_PLY);
        let history_start = game_hashes.len() - self.hash_len;
        self.hashes[..self.hash_len].copy_from_slice(&game_hashes[history_start..]);
        let mut legal = MoveList::new();
        generate_legal(pos, &mut legal, false);
        if legal.len == 0 {
            return 0;
        }
        if self.own_book
            && let Some(book) = opening_move(pos)
        {
            if (0..legal.len).any(|i| legal.moves[i] == book) {
                if !self.silent {
                    println!("info string book {}", move_to_uci(book));
                }
                return book;
            }
        }
        let mut completed_move = legal.moves[0];
        let mut completed_score = 0;
        let mut previous_score = 0;
        for depth in 1..=limits.depth.min(64) {
            if depth > 1
                && self
                    .soft_limit
                    .is_some_and(|limit| self.started.elapsed() >= limit)
            {
                break;
            }
            let window = if depth >= 4 { 35 } else { INF };
            let iteration_started = Instant::now();
            let mut alpha = (previous_score - window).max(-INF);
            let mut beta = (previous_score + window).min(INF);
            let (mut score, mut best) = self.root_search(pos, depth, alpha, beta);
            if !self.stopped && (score <= alpha || score >= beta) {
                alpha = -INF;
                beta = INF;
                (score, best) = self.root_search(pos, depth, alpha, beta);
            }
            if self.stopped {
                break;
            }
            completed_move = best;
            completed_score = score;
            previous_score = score;
            let elapsed = self.started.elapsed();
            let iteration_time = iteration_started.elapsed();
            let nps = if elapsed.as_millis() > 0 {
                self.nodes * 1000 / elapsed.as_millis() as u64
            } else {
                self.nodes
            };
            if !self.silent {
                let score_text = if score.abs() > MATE - MAX_PLY as i32 {
                    format!(
                        "score mate {}",
                        if score > 0 {
                            (MATE - score + 1) / 2
                        } else {
                            -(MATE + score) / 2
                        }
                    )
                } else {
                    format!("score cp {}", score)
                };
                println!(
                    "info depth {} seldepth {} {} nodes {} nps {} time {} pv {}",
                    depth,
                    self.seldepth,
                    score_text,
                    self.nodes,
                    nps,
                    elapsed.as_millis(),
                    move_to_uci(best)
                );
            }
            if score.abs() > MATE - 100
                || limits
                    .soft
                    .is_some_and(|limit| elapsed + iteration_time * 2 >= limit)
            {
                break;
            }
        }
        let _ = completed_score;
        // A TT collision or interrupted iteration can never bypass final legal validation.
        if (0..legal.len).any(|i| legal.moves[i] == completed_move) {
            completed_move
        } else {
            legal.moves[0]
        }
    }
}

#[derive(Clone, Copy)]
struct GoLimits {
    depth: i32,
    soft: Option<Duration>,
    hard: Option<Duration>,
    nodes: Option<u64>,
}

fn parse_go(command: &str, side: i8) -> GoLimits {
    let words: Vec<&str> = command.split_whitespace().collect();
    let mut depth = 64;
    let mut movetime = None;
    let mut wtime = None;
    let mut btime = None;
    let mut winc = 0u64;
    let mut binc = 0u64;
    let mut moves_to_go = 0u64;
    let mut nodes = None;
    let mut i = 1;
    while i < words.len() {
        let value = words.get(i + 1).and_then(|v| v.parse::<u64>().ok());
        match words[i] {
            "depth" => {
                if let Some(v) = value {
                    depth = v.min(64) as i32;
                }
                i += 1;
            }
            "movetime" => {
                movetime = value;
                i += 1;
            }
            "wtime" => {
                wtime = value;
                i += 1;
            }
            "btime" => {
                btime = value;
                i += 1;
            }
            "winc" => {
                winc = value.unwrap_or(0);
                i += 1;
            }
            "binc" => {
                binc = value.unwrap_or(0);
                i += 1;
            }
            "movestogo" => {
                moves_to_go = value.unwrap_or(0);
                i += 1;
            }
            "nodes" => {
                nodes = value;
                i += 1;
            }
            "infinite" => {}
            _ => {}
        }
        i += 1;
    }
    if let Some(ms) = movetime {
        let hard_ms = ms.saturating_sub(3).max(1);
        return GoLimits {
            depth,
            soft: Some(Duration::from_millis((hard_ms * 9 / 10).max(1))),
            hard: Some(Duration::from_millis(hard_ms)),
            nodes,
        };
    }
    let remain = if side == WHITE { wtime } else { btime };
    let inc = if side == WHITE { winc } else { binc };
    if let Some(ms) = remain {
        let overhead = 8u64.min(ms / 5);
        let usable = ms.saturating_sub(overhead).max(1);
        let divisor = if moves_to_go > 0 {
            moves_to_go.min(40)
        } else {
            25
        };
        let target = (usable / divisor + inc * 3 / 4).min(usable);
        let hard = (target * 3).min(usable).max(1);
        GoLimits {
            depth,
            soft: Some(Duration::from_millis(target.max(1))),
            hard: Some(Duration::from_millis(hard)),
            nodes,
        }
    } else {
        GoLimits {
            depth,
            soft: None,
            hard: None,
            nodes,
        }
    }
}

fn set_position(command: &str, pos: &mut Position, history: &mut Vec<u64>) -> Result<(), String> {
    let words: Vec<&str> = command.split_whitespace().collect();
    if words.len() < 2 {
        return Err("missing position".into());
    }
    let (mut next, mut move_index) = if words[1] == "startpos" {
        (Position::from_fen(START_FEN)?, 2)
    } else if words[1] == "fen" {
        let moves_at = words
            .iter()
            .position(|&w| w == "moves")
            .unwrap_or(words.len());
        if moves_at < 6 {
            return Err("incomplete FEN".into());
        }
        (Position::from_fen(&words[2..moves_at].join(" "))?, moves_at)
    } else {
        return Err("position must use startpos or fen".into());
    };
    let mut next_history = vec![next.hash];
    if words.get(move_index) == Some(&"moves") {
        move_index += 1;
    }
    while move_index < words.len() {
        let mv = parse_uci_move(&mut next, words[move_index])
            .ok_or_else(|| format!("illegal move {}", words[move_index]))?;
        next.make_move(mv);
        next_history.push(next.hash);
        move_index += 1;
    }
    *pos = next;
    *history = next_history;
    Ok(())
}

fn run_perft(fen: &str, depth: u32, divide: bool) -> Result<u64, String> {
    let mut pos = Position::from_fen(fen)?;
    let started = Instant::now();
    let nodes = if divide && depth > 0 {
        let mut list = MoveList::new();
        generate_legal(&mut pos, &mut list, false);
        let mut total = 0;
        for i in 0..list.len {
            let mv = list.moves[i];
            let undo = pos.make_move(mv);
            let count = perft(&mut pos, depth - 1);
            pos.unmake_move(mv, undo);
            println!("{}: {}", move_to_uci(mv), count);
            total += count;
        }
        total
    } else {
        perft(&mut pos, depth)
    };
    let elapsed = started.elapsed();
    let nps = if elapsed.as_micros() > 0 {
        nodes as u128 * 1_000_000 / elapsed.as_micros()
    } else {
        nodes as u128
    };
    println!("nodes {} time {} nps {}", nodes, elapsed.as_millis(), nps);
    Ok(nodes)
}

fn run_tests() -> Result<(), String> {
    let suites = [
        (START_FEN, 5, 4_865_609u64),
        (
            "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
            4,
            4_085_603,
        ),
        ("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 5, 674_624),
        (
            "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
            4,
            422_333,
        ),
        (
            "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8",
            4,
            2_103_487,
        ),
        (
            "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
            4,
            3_894_594,
        ),
    ];
    for (fen, depth, expected) in suites {
        let mut pos = Position::from_fen(fen)?;
        let started = Instant::now();
        let got = perft(&mut pos, depth);
        if got != expected {
            return Err(format!(
                "perft failed depth {}: got {}, expected {} ({})",
                depth, got, expected, fen
            ));
        }
        println!(
            "perft depth {} nodes {} ok ({} ms)",
            depth,
            got,
            started.elapsed().as_millis()
        );
    }
    let mut seed = 0x1234_5678_9ABC_DEF0u64;
    for game in 0..100 {
        let mut pos = Position::from_fen(START_FEN)?;
        for _ply in 0..160 {
            let before = pos.clone();
            let mut list = MoveList::new();
            generate_legal(&mut pos, &mut list, false);
            if list.len == 0 {
                break;
            }
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let mv = list.moves[seed as usize % list.len];
            let undo = pos.make_move(mv);
            let after = pos.clone();
            pos.unmake_move(mv, undo);
            if pos != before {
                return Err(format!("make/unmake mismatch in game {}", game));
            }
            let old_hash = after.hash;
            pos = after;
            pos.recompute_state();
            if pos.hash != old_hash {
                return Err(format!("incremental hash mismatch in game {}", game));
            }
        }
    }
    println!("state 100 random games make/unmake/hash ok");
    let tactical = [
        ("7k/5Q2/6K1/8/8/8/8/8 w - - 0 1", 3, "f7g7"),
        ("6k1/5ppp/8/8/8/8/5PPP/3Q2K1 w - - 0 1", 4, "d1d8"),
        ("4k3/8/3q4/8/2N5/8/8/4K3 w - - 0 1", 5, "c4d6"),
    ];
    let stop = Arc::new(AtomicBool::new(false));
    let mut searcher = Searcher::new(16, stop);
    for (fen, depth, expected) in tactical {
        let mut pos = Position::from_fen(fen)?;
        let hashes = [pos.hash];
        let mv = searcher.search(
            &mut pos,
            GoLimits {
                depth,
                soft: None,
                hard: None,
                nodes: None,
            },
            &hashes,
        );
        if mv == 0 {
            return Err("tactical search returned no move".into());
        }
        let mut legal = MoveList::new();
        generate_legal(&mut pos, &mut legal, false);
        if !(0..legal.len).any(|i| legal.moves[i] == mv) {
            return Err("tactical search returned illegal move".into());
        }
        if move_to_uci(mv) != expected {
            return Err(format!(
                "tactical failed: got {}, expected {}",
                move_to_uci(mv),
                expected
            ));
        }
        println!("tactical {} bestmove {} ok", fen, move_to_uci(mv));
    }
    Ok(())
}

fn run_bench(depth: i32) -> Result<(), String> {
    let positions = [
        START_FEN,
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
        "2r2rk1/1bqnbppp/p2ppn2/1p6/3NP3/P1N1B3/1PQ1BPPP/2RR2K1 w - - 0 1",
        "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
    ];
    let stop = Arc::new(AtomicBool::new(false));
    let mut searcher = Searcher::new(64, stop);
    searcher.own_book = false;
    let started = Instant::now();
    let mut nodes = 0u64;
    for fen in positions {
        let mut pos = Position::from_fen(fen)?;
        let hashes = [pos.hash];
        let mv = searcher.search(
            &mut pos,
            GoLimits {
                depth,
                soft: None,
                hard: None,
                nodes: None,
            },
            &hashes,
        );
        println!(
            "bench bestmove {} nodes {}",
            move_to_uci(mv),
            searcher.nodes
        );
        nodes += searcher.nodes;
    }
    let elapsed = started.elapsed();
    let nps = nodes * 1000 / elapsed.as_millis().max(1) as u64;
    println!(
        "bench depth {} nodes {} time {} nps {}",
        depth,
        nodes,
        elapsed.as_millis(),
        nps
    );
    Ok(())
}

fn run_selfplay(depth: i32, max_plies: usize) -> Result<(), String> {
    let stop = Arc::new(AtomicBool::new(false));
    let mut searcher = Searcher::new(32, stop);
    searcher.silent = true;
    let mut pos = Position::from_fen(START_FEN)?;
    let mut history = vec![pos.hash];
    let mut played = Vec::new();
    for _ in 0..max_plies {
        if web_game_over(&mut pos, &history) {
            break;
        }
        let mut legal = MoveList::new();
        generate_legal(&mut pos, &mut legal, false);
        let mv = searcher.search(
            &mut pos,
            GoLimits {
                depth,
                soft: None,
                hard: None,
                nodes: None,
            },
            &history,
        );
        if !(0..legal.len).any(|i| legal.moves[i] == mv) {
            return Err("self-play produced an illegal move".into());
        }
        played.push(move_to_uci(mv));
        pos.make_move(mv);
        history.push(pos.hash);
        let expected = pos.clone();
        pos.recompute_state();
        if pos.hash != expected.hash
            || pos.mg != expected.mg
            || pos.eg != expected.eg
            || pos.phase != expected.phase
        {
            return Err("self-play incremental state mismatch".into());
        }
    }
    println!("selfplay plies {} moves {}", played.len(), played.join(" "));
    Ok(())
}

fn web_position(serialized_moves: &str) -> Result<(Position, Vec<u64>), String> {
    let mut pos = Position::from_fen(START_FEN)?;
    let mut history = vec![pos.hash];
    if serialized_moves != "-" && !serialized_moves.is_empty() {
        for text in serialized_moves.split(',') {
            if web_game_over(&mut pos, &history) {
                return Err(format!("move after game over in history: {text}"));
            }
            let mv = parse_uci_move(&mut pos, text)
                .ok_or_else(|| format!("illegal move in history: {text}"))?;
            pos.make_move(mv);
            history.push(pos.hash);
        }
    }
    Ok((pos, history))
}

fn web_threefold(history: &[u64], current: u64) -> bool {
    history.iter().filter(|&&hash| hash == current).count() >= 3
}

fn web_game_over(pos: &mut Position, history: &[u64]) -> bool {
    if pos.halfmove >= 100 || insufficient_material(pos) || web_threefold(history, pos.hash) {
        return true;
    }
    !has_legal_move(pos)
}

fn web_snapshot(pos: &mut Position, history: &[u64], engine_move: Option<u32>) -> String {
    let in_check = pos.in_check(pos.side);
    let mut legal = MoveList::new();
    generate_legal(pos, &mut legal, false);
    let status = if legal.len == 0 {
        if in_check { "checkmate" } else { "stalemate" }
    } else if pos.halfmove >= 100 || insufficient_material(pos) || web_threefold(history, pos.hash)
    {
        "draw"
    } else if in_check {
        "check"
    } else {
        "playing"
    };
    let moves = if matches!(status, "checkmate" | "stalemate" | "draw") {
        String::new()
    } else {
        (0..legal.len)
            .map(|i| format!("\"{}\"", move_to_uci(legal.moves[i])))
            .collect::<Vec<_>>()
            .join(",")
    };
    let engine = engine_move
        .map(|mv| format!("\"{}\"", move_to_uci(mv)))
        .unwrap_or_else(|| "null".into());
    format!(
        "{{\"ok\":true,\"fen\":\"{}\",\"side\":\"{}\",\"status\":\"{}\",\"inCheck\":{},\"legal\":[{}],\"engineMove\":{}}}",
        pos.to_fen(),
        if pos.side == WHITE { "w" } else { "b" },
        status,
        in_check,
        moves,
        engine
    )
}

fn web_error(message: &str) -> String {
    let escaped = message.replace('\\', "\\\\").replace('"', "\\\"");
    format!("{{\"ok\":false,\"error\":\"{escaped}\"}}")
}

fn run_web(args: &[String]) -> Result<(), String> {
    let result = (|| -> Result<String, String> {
        let action = args
            .first()
            .map(String::as_str)
            .ok_or("missing web action")?;
        let moves = args.get(1).map(String::as_str).unwrap_or("-");
        let (mut pos, mut history) = web_position(moves)?;
        match action {
            "state" => Ok(web_snapshot(&mut pos, &history, None)),
            "play" => {
                if web_game_over(&mut pos, &history) {
                    return Err("game is already over".into());
                }
                let text = args.get(2).ok_or("missing player move")?;
                let mv = parse_uci_move(&mut pos, text).ok_or("illegal player move")?;
                pos.make_move(mv);
                history.push(pos.hash);
                Ok(web_snapshot(&mut pos, &history, None))
            }
            "engine" => {
                let mut legal = MoveList::new();
                generate_legal(&mut pos, &mut legal, false);
                if legal.len == 0 || web_game_over(&mut pos, &history) {
                    return Ok(web_snapshot(&mut pos, &history, None));
                }
                let think_ms = args
                    .get(2)
                    .and_then(|value| value.parse::<u64>().ok())
                    .unwrap_or(650)
                    .clamp(25, 5_000);
                let stop = Arc::new(AtomicBool::new(false));
                let mut searcher = Searcher::new(16, stop);
                searcher.silent = true;
                let hard_ms = think_ms.saturating_sub(4).max(1);
                let best = searcher.search(
                    &mut pos,
                    GoLimits {
                        depth: 64,
                        soft: Some(Duration::from_millis(hard_ms * 9 / 10)),
                        hard: Some(Duration::from_millis(hard_ms)),
                        nodes: None,
                    },
                    &history,
                );
                if !(0..legal.len).any(|i| legal.moves[i] == best) {
                    return Err("engine returned an illegal move".into());
                }
                pos.make_move(best);
                history.push(pos.hash);
                Ok(web_snapshot(&mut pos, &history, Some(best)))
            }
            _ => Err("unknown web action".into()),
        }
    })();
    println!("{}", result.unwrap_or_else(|error| web_error(&error)));
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn uci_loop() -> Result<(), String> {
    let stop = Arc::new(AtomicBool::new(false));
    let reader_stop = stop.clone();
    let (tx, rx) = mpsc::channel::<String>();
    std::thread::spawn(move || {
        let stdin = io::stdin();
        for line in stdin.lock().lines().map_while(Result::ok) {
            if matches!(line.trim(), "stop" | "quit") {
                reader_stop.store(true, Ordering::Relaxed);
            }
            if tx.send(line).is_err() {
                break;
            }
        }
    });
    let mut pos = Position::from_fen(START_FEN)?;
    let mut history = vec![pos.hash];
    let mut hash_mb = 64usize;
    let mut searcher = Searcher::new(hash_mb, stop.clone());
    while let Ok(line) = rx.recv() {
        let command = line.trim();
        if command == "uci" {
            println!("id name Warhorse 1.0");
            println!("id author OpenCode");
            println!("option name Hash type spin default 64 min 1 max 512");
            println!("option name OwnBook type check default true");
            println!("uciok");
        } else if command == "isready" {
            println!("readyok");
        } else if command == "ucinewgame" {
            pos = Position::from_fen(START_FEN)?;
            history.clear();
            history.push(pos.hash);
            searcher.tt = TransTable::new(hash_mb);
            searcher.killers = [[0; 2]; MAX_PLY];
            searcher.history = [[0; 64]; 12];
            searcher.counter = [0; 4096];
        } else if command.starts_with("setoption name Hash value ") {
            if let Some(value) = command
                .split_whitespace()
                .last()
                .and_then(|s| s.parse::<usize>().ok())
            {
                hash_mb = value.clamp(1, 512);
                searcher.tt = TransTable::new(hash_mb);
            }
        } else if command.starts_with("setoption name OwnBook value ") {
            searcher.own_book = command.ends_with("true");
        } else if command.starts_with("position ") {
            if let Err(error) = set_position(command, &mut pos, &mut history) {
                eprintln!("position error: {}", error);
            }
        } else if command.starts_with("go") {
            let limits = parse_go(command, pos.side);
            let best = searcher.search(&mut pos, limits, &history);
            println!(
                "bestmove {}",
                if best == 0 {
                    "0000".into()
                } else {
                    move_to_uci(best)
                }
            );
        } else if command == "stop" {
            stop.store(false, Ordering::Relaxed);
        } else if command == "quit" {
            break;
        } else if command == "d" {
            eprintln!("fen hash {:016x} eval {}", pos.hash, evaluate(&pos));
        }
    }
    Ok(())
}

#[cfg(target_arch = "wasm32")]
fn uci_loop() -> Result<(), String> {
    let stop = Arc::new(AtomicBool::new(false));
    let mut pos = Position::from_fen(START_FEN)?;
    let mut history = vec![pos.hash];
    let mut hash_mb = 64usize;
    let mut searcher = Searcher::new(hash_mb, stop.clone());
    let stdin = io::stdin();
    for line in stdin.lock().lines().map_while(Result::ok) {
        let command = line.trim();
        if command == "uci" {
            println!("id name Warhorse 1.0");
            println!("id author OpenCode");
            println!("option name Hash type spin default 64 min 1 max 512");
            println!("option name OwnBook type check default true");
            println!("uciok");
        } else if command == "isready" {
            println!("readyok");
        } else if command == "ucinewgame" {
            pos = Position::from_fen(START_FEN)?;
            history.clear();
            history.push(pos.hash);
            searcher.tt = TransTable::new(hash_mb);
            searcher.killers = [[0; 2]; MAX_PLY];
            searcher.history = [[0; 64]; 12];
            searcher.counter = [0; 4096];
        } else if command.starts_with("setoption name Hash value ") {
            if let Some(value) = command
                .split_whitespace()
                .last()
                .and_then(|s| s.parse::<usize>().ok())
            {
                hash_mb = value.clamp(1, 512);
                searcher.tt = TransTable::new(hash_mb);
            }
        } else if command.starts_with("setoption name OwnBook value ") {
            searcher.own_book = command.ends_with("true");
        } else if command.starts_with("position ") {
            if let Err(error) = set_position(command, &mut pos, &mut history) {
                eprintln!("position error: {}", error);
            }
        } else if command.starts_with("go") {
            stop.store(false, Ordering::Relaxed);
            let limits = parse_go(command, pos.side);
            let best = searcher.search(&mut pos, limits, &history);
            println!(
                "bestmove {}",
                if best == 0 {
                    "0000".into()
                } else {
                    move_to_uci(best)
                }
            );
        } else if command == "quit" {
            break;
        }
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let result = match args.get(1).map(String::as_str) {
        Some("perft") | Some("--perft") => {
            let depth = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
            let fen = args.get(3).map(String::as_str).unwrap_or(START_FEN);
            run_perft(fen, depth, true).map(|_| ())
        }
        Some("test") | Some("--test") => run_tests(),
        Some("bench") | Some("--bench") => {
            run_bench(args.get(2).and_then(|s| s.parse().ok()).unwrap_or(7))
        }
        Some("selfplay") | Some("--selfplay") => run_selfplay(
            args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5),
            args.get(3).and_then(|s| s.parse().ok()).unwrap_or(80),
        ),
        Some("web") => run_web(&args[2..]),
        _ => uci_loop(),
    };
    if let Err(error) = result {
        eprintln!("error: {}", error);
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn legal_uci(pos: &mut Position) -> Vec<String> {
        let mut list = MoveList::new();
        generate_legal(pos, &mut list, false);
        (0..list.len)
            .map(|index| move_to_uci(list.moves[index]))
            .collect()
    }

    fn play(pos: &mut Position, text: &str) -> Undo {
        let mv = parse_uci_move(pos, text).unwrap_or_else(|| panic!("expected legal move {text}"));
        pos.make_move(mv)
    }

    fn play_line(pos: &mut Position, moves: &[&str]) -> Vec<u64> {
        let mut history = vec![pos.hash];
        for text in moves {
            play(pos, text);
            history.push(pos.hash);
        }
        history
    }

    #[test]
    fn basic_pawn_rules_and_turn_switching() {
        let mut pos = Position::from_fen(START_FEN).unwrap();
        let legal = legal_uci(&mut pos);
        assert_eq!(legal.len(), 20);
        for expected in ["a2a3", "a2a4", "e2e3", "e2e4"] {
            assert!(legal.contains(&expected.to_string()));
        }
        for illegal in ["a2a5", "e2e1", "e2f3", "e7e5", "e2e4q", "€a"] {
            assert!(parse_uci_move(&mut pos, illegal).is_none(), "{illegal}");
        }
        play(&mut pos, "e2e4");
        assert_eq!(pos.side, BLACK);
        assert_eq!(pos.ep, parse_square("e3").unwrap() as i8);
        assert_eq!(pos.halfmove, 0);
        assert_eq!(pos.fullmove, 1);
        play(&mut pos, "c7c5");
        assert_eq!(pos.side, WHITE);
        assert_eq!(pos.fullmove, 2);
    }

    #[test]
    fn piece_movement_and_sliding_obstruction() {
        let mut start = Position::from_fen(START_FEN).unwrap();
        let legal = legal_uci(&mut start);
        assert!(legal.contains(&"b1a3".into()) && legal.contains(&"g1f3".into()));
        assert!(!legal.iter().any(|mv| mv.starts_with("c1")));
        assert!(!legal.iter().any(|mv| mv.starts_with("a1")));
        assert!(!legal.iter().any(|mv| mv.starts_with("d1")));

        let mut sliders = Position::from_fen("4k3/8/8/3p4/3Q4/4P3/8/4K3 w - - 0 1").unwrap();
        let legal = legal_uci(&mut sliders);
        assert!(legal.contains(&"d4d5".into()));
        assert!(!legal.contains(&"d4d6".into()));
        assert!(!legal.contains(&"d4e3".into()));
        assert!(legal.contains(&"d4a4".into()));
        assert!(legal.contains(&"d4h4".into()));

        let mut bishop = Position::from_fen("4k3/8/8/8/8/4P3/3B4/4K3 w - - 0 1").unwrap();
        let legal = legal_uci(&mut bishop);
        assert!(!legal.contains(&"d2e3".into()));
        assert!(!legal.contains(&"d2f4".into()));

        let mut rook = Position::from_fen("4k3/8/8/8/8/8/P7/R3K3 w - - 0 1").unwrap();
        let legal = legal_uci(&mut rook);
        assert!(!legal.contains(&"a1a2".into()));
        assert!(!legal.contains(&"a1a8".into()));
    }

    #[test]
    fn pins_checks_and_king_safety_are_enforced() {
        let mut pinned = Position::from_fen("4r1k1/8/8/8/8/8/4N3/4K3 w - - 0 1").unwrap();
        assert!(pinned.in_check(WHITE) == false);
        assert!(!legal_uci(&mut pinned).iter().any(|mv| mv.starts_with("e2")));

        let mut checked = Position::from_fen("4r1k1/8/8/8/8/8/4r3/4K3 w - - 0 1").unwrap();
        assert!(checked.in_check(WHITE));
        assert!(parse_uci_move(&mut checked, "e1e2").is_none());

        let mut king = Position::from_fen("3r2k1/8/8/8/8/8/3r4/4K3 w - - 0 1").unwrap();
        assert!(parse_uci_move(&mut king, "e1d2").is_none());

        let mut safe_king = Position::from_fen("7k/8/8/8/8/8/8/4K3 w - - 0 1").unwrap();
        assert!(parse_uci_move(&mut safe_king, "e1d1").is_some());
        assert!(parse_uci_move(&mut safe_king, "e1e2").is_some());
    }

    #[test]
    fn checkmate_stalemate_and_normal_play_are_distinct() {
        let mut mate = Position::from_fen(START_FEN).unwrap();
        let history = play_line(&mut mate, &["f2f3", "e7e5", "g2g4", "d8h4"]);
        assert!(mate.in_check(WHITE));
        assert!(!has_legal_move(&mut mate));
        assert!(web_snapshot(&mut mate, &history, None).contains("\"status\":\"checkmate\""));

        let mut stale = Position::from_fen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1").unwrap();
        let hash = stale.hash;
        assert!(!stale.in_check(BLACK));
        assert!(!has_legal_move(&mut stale));
        assert!(web_snapshot(&mut stale, &[hash], None).contains("\"status\":\"stalemate\""));

        let mut normal = Position::from_fen(START_FEN).unwrap();
        let hash = normal.hash;
        assert!(web_snapshot(&mut normal, &[hash], None).contains("\"status\":\"playing\""));
    }

    #[test]
    fn castling_and_rights_transitions_are_correct() {
        let fen = "r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1";
        let mut pos = Position::from_fen(fen).unwrap();
        let legal = legal_uci(&mut pos);
        assert!(legal.contains(&"e1g1".into()));
        assert!(legal.contains(&"e1c1".into()));
        play(&mut pos, "e1g1");
        assert_eq!(pos.board[parse_square("g1").unwrap() as usize], KING);
        assert_eq!(pos.board[parse_square("f1").unwrap() as usize], ROOK);
        assert_eq!(pos.castle & 3, 0);

        let mut black = Position::from_fen("r3k2r/8/8/8/8/8/8/R3K2R b KQkq - 0 1").unwrap();
        assert!(legal_uci(&mut black).contains(&"e8c8".into()));
        play(&mut black, "e8c8");
        assert_eq!(black.board[parse_square("c8").unwrap() as usize], -KING);
        assert_eq!(black.board[parse_square("d8").unwrap() as usize], -ROOK);

        let mut through_check = Position::from_fen("4k3/8/8/8/2b5/8/8/4K2R w K - 0 1").unwrap();
        assert!(!legal_uci(&mut through_check).contains(&"e1g1".into()));

        let mut king_moved = Position::from_fen(fen).unwrap();
        play(&mut king_moved, "e1f1");
        assert_eq!(king_moved.castle & 3, 0);

        let mut rook_moved = Position::from_fen(fen).unwrap();
        play(&mut rook_moved, "h1h2");
        assert_eq!(rook_moved.castle & 1, 0);
        assert_ne!(rook_moved.castle & 2, 0);

        let mut rook_captured = Position::from_fen("4k3/8/8/8/8/8/q7/R3K3 b Q - 0 1").unwrap();
        play(&mut rook_captured, "a2a1");
        assert_eq!(rook_captured.castle & 2, 0);
    }

    #[test]
    fn en_passant_creation_capture_expiry_and_king_safety() {
        let mut pos = Position::from_fen(START_FEN).unwrap();
        play_line(&mut pos, &["e2e4", "a7a6", "e4e5", "d7d5"]);
        assert!(legal_uci(&mut pos).contains(&"e5d6".into()));
        let undo = play(&mut pos, "e5d6");
        assert_eq!(undo.captured, -PAWN);
        assert_eq!(pos.board[parse_square("d6").unwrap() as usize], PAWN);
        assert_eq!(pos.board[parse_square("d5").unwrap() as usize], EMPTY);

        let mut expires = Position::from_fen(START_FEN).unwrap();
        play_line(
            &mut expires,
            &["e2e4", "a7a6", "e4e5", "d7d5", "a2a3", "a6a5"],
        );
        assert!(!legal_uci(&mut expires).contains(&"e5d6".into()));

        let mut pinned = Position::from_fen("4r1k1/8/8/3pP3/8/8/8/4K3 w - d6 0 1").unwrap();
        assert!(!legal_uci(&mut pinned).contains(&"e5d6".into()));
    }

    #[test]
    fn promotion_replaces_pawn_and_capture_state_is_reversible() {
        let mut promotion = Position::from_fen("7k/1P6/8/8/8/8/8/7K w - - 0 1").unwrap();
        let legal = legal_uci(&mut promotion);
        for suffix in ['q', 'r', 'b', 'n'] {
            assert!(legal.contains(&format!("b7b8{suffix}")));
        }
        play(&mut promotion, "b7b8n");
        assert_eq!(
            promotion.board[parse_square("b8").unwrap() as usize],
            KNIGHT
        );
        assert_eq!(promotion.board[parse_square("b7").unwrap() as usize], EMPTY);

        let mut capture = Position::from_fen("4k3/8/8/8/8/8/4p3/4R1K1 w - - 0 1").unwrap();
        let before = capture.clone();
        let mv = parse_uci_move(&mut capture, "e1e2").unwrap();
        let undo = capture.make_move(mv);
        assert_eq!(undo.captured, -PAWN);
        assert_eq!(capture.board[parse_square("e2").unwrap() as usize], ROOK);
        assert_eq!(capture.board[parse_square("e1").unwrap() as usize], EMPTY);
        capture.unmake_move(mv, undo);
        assert_eq!(capture, before);
    }

    #[test]
    fn fen_rejects_impossible_rule_state() {
        assert!(Position::from_fen("4k3/8/8/8/8/8/8/4K3 w - -").is_err());
        assert!(Position::from_fen("4k3/8/8/8/8/8/8/4K3 w - - 0 1 extra").is_err());
        assert!(Position::from_fen("4k3/8/8/8/8/8/7R/4K3 w K - 0 1").is_err());
        assert!(Position::from_fen("4k3/4n3/8/4pP2/8/8/8/4K3 w - e6 0 1").is_err());
        assert!(Position::from_fen("4k3/8/8/4pP2/8/8/8/4K3 w - e6 1 1").is_err());
    }

    #[test]
    fn two_knights_are_not_automatically_dead_material() {
        let live = Position::from_fen("7k/8/5NN1/8/8/8/8/5K2 w - - 0 1").unwrap();
        assert!(!insufficient_material(&live));
        let mut mate = Position::from_fen("7k/5K2/5NN1/8/8/8/8/8 b - - 0 1").unwrap();
        assert!(mate.in_check(BLACK));
        assert!(!has_legal_move(&mut mate));
    }

    #[test]
    fn web_history_rejects_moves_after_terminal_positions() {
        let repeated = "g1f3,g8f6,f3g1,f6g8,g1f3,g8f6,f3g1,f6g8";
        let (mut pos, history) = web_position(repeated).unwrap();
        assert!(web_snapshot(&mut pos, &history, None).contains("\"status\":\"draw\""));
        assert!(web_position(&format!("{repeated},e2e4")).is_err());
    }

    #[test]
    fn null_move_and_search_restore_state_and_history() {
        let mut pos = Position::from_fen("4k3/8/8/8/8/8/4Q3/4K3 w - - 37 1").unwrap();
        let before = pos.clone();
        let undo = pos.make_null();
        assert_eq!(pos.side, BLACK);
        assert_eq!(pos.halfmove, 38);
        assert_eq!(pos.ep, -1);
        pos.unmake_null(undo);
        assert_eq!(pos, before);

        let stop = Arc::new(AtomicBool::new(false));
        let mut searcher = Searcher::new(1, stop);
        searcher.own_book = false;
        let history = [11, 22, 33, 44, before.hash];
        let best = searcher.search(
            &mut pos,
            GoLimits {
                depth: 5,
                soft: None,
                hard: None,
                nodes: None,
            },
            &history,
        );
        assert_ne!(best, 0);
        assert_eq!(&searcher.hashes[..history.len()], &history);
        assert_eq!(searcher.null_depth, 0);
        assert_eq!(pos, before);
    }

    #[test]
    fn every_opening_book_entry_is_legal() {
        for (line, choice) in OPENING_BOOK {
            let mut pos = Position::from_fen(START_FEN).unwrap();
            for text in line.split_whitespace() {
                play(&mut pos, text);
            }
            let expected = parse_uci_move(&mut pos, choice)
                .unwrap_or_else(|| panic!("invalid book move {choice} after {line}"));
            assert_eq!(opening_move(&mut pos), Some(expected));
        }
    }

    #[test]
    fn bounded_search_returns_a_legal_move() {
        let mut pos = Position::from_fen(
            "r1bqk2r/pppp1ppp/2n2n2/4p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R w KQkq - 4 4",
        )
        .unwrap();
        let hash = pos.hash;
        let mut legal = MoveList::new();
        generate_legal(&mut pos, &mut legal, false);
        let stop = Arc::new(AtomicBool::new(false));
        let mut searcher = Searcher::new(1, stop);
        searcher.own_book = false;
        let best = searcher.search(
            &mut pos,
            GoLimits {
                depth: 16,
                soft: None,
                hard: None,
                nodes: Some(1),
            },
            &[hash],
        );
        assert!(searcher.nodes <= 1);
        assert!((0..legal.len).any(|index| legal.moves[index] == best));
    }

    #[test]
    fn tactical_search_finds_forcing_moves() {
        let cases = [
            ("7k/5Q2/6K1/8/8/8/8/8 w - - 0 1", 3, "f7g7"),
            ("6k1/5ppp/8/8/8/8/5PPP/3Q2K1 w - - 0 1", 4, "d1d8"),
            ("4k3/8/3q4/8/2N5/8/8/4K3 w - - 0 1", 5, "c4d6"),
        ];
        for (fen, depth, expected) in cases {
            let stop = Arc::new(AtomicBool::new(false));
            let mut searcher = Searcher::new(4, stop);
            searcher.own_book = false;
            let mut pos = Position::from_fen(fen).unwrap();
            let hash = pos.hash;
            let best = searcher.search(
                &mut pos,
                GoLimits {
                    depth,
                    soft: None,
                    hard: None,
                    nodes: None,
                },
                &[hash],
            );
            assert_eq!(move_to_uci(best), expected, "{fen}");
        }
    }

    #[test]
    fn legal_see_ignores_pinned_and_illegal_king_recaptures() {
        let mut pinned = Position::from_fen("4k3/3pr3/8/8/8/8/8/3QR1K1 w - - 0 1").unwrap();
        let capture = parse_uci_move(&mut pinned, "d1d7").unwrap();
        assert!(see(&pinned, capture) < 0);

        let mut king = Position::from_fen("7k/6r1/8/8/8/2B5/6Q1/K7 w - - 0 1").unwrap();
        let capture = parse_uci_move(&mut king, "g2g7").unwrap();
        assert!(see(&king, capture) >= PIECE_VALUE[ROOK as usize]);

        let mut recapture_promotion =
            Position::from_fen("r1b4k/1P6/8/8/8/7Q/8/7K w - - 0 1").unwrap();
        let capture = parse_uci_move(&mut recapture_promotion, "h3c8").unwrap();
        assert!(see(&recapture_promotion, capture) > 0);
    }

    #[test]
    fn selective_search_regression_positions() {
        let cases = [
            (
                "rnbbk2r/pp1p2pp/2p1p2n/5Q1R/8/3P2P1/PPP1PP2/RNBK1BN1 w kq - 1 9",
                4,
                "f5h3",
            ),
            (
                "r1bk2nr/p1p2p2/1p2p1n1/3p2p1/2PP4/N2BP2P/P4PP1/2RK2R1 w - - 1 18",
                4,
                "c4d5",
            ),
            (
                "1nb1kb2/1p1p1pp1/1q2pn2/7r/rp3P2/3P2PN/PB2P2P/RN1QK2R b KQ - 1 13",
                4,
                "b4b3",
            ),
        ];
        for (fen, depth, expected) in cases {
            let stop = Arc::new(AtomicBool::new(false));
            let mut searcher = Searcher::new(4, stop);
            searcher.own_book = false;
            let mut pos = Position::from_fen(fen).unwrap();
            let hash = pos.hash;
            let best = searcher.search(
                &mut pos,
                GoLimits {
                    depth,
                    soft: None,
                    hard: None,
                    nodes: None,
                },
                &[hash],
            );
            assert_eq!(move_to_uci(best), expected, "{fen}");
        }
    }

    #[test]
    fn evaluation_and_time_controls_have_expected_direction() {
        let white_to_move = Position::from_fen("4k3/8/8/8/8/8/4Q3/4K3 w - - 0 1").unwrap();
        let black_to_move = Position::from_fen("4k3/8/8/8/8/8/4Q3/4K3 b - - 0 1").unwrap();
        assert!(evaluate(&white_to_move) > 800);
        assert!(evaluate(&black_to_move) < -800);

        let quick = parse_go("go movetime 250", WHITE);
        let deep = parse_go("go movetime 2500", WHITE);
        assert!(quick.soft < deep.soft);
        assert!(quick.hard < deep.hard);
        assert_eq!(quick.hard, Some(Duration::from_millis(247)));
        assert_eq!(deep.hard, Some(Duration::from_millis(2497)));
    }

    #[test]
    fn canonical_perft_regression() {
        let mut start = Position::from_fen(START_FEN).unwrap();
        assert_eq!(perft(&mut start, 4), 197_281);
        let mut kiwipete = Position::from_fen(
            "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
        )
        .unwrap();
        assert_eq!(perft(&mut kiwipete, 3), 97_862);
    }

    #[test]
    fn adversarial_move_generation() {
        let cases = [
            ("8/6bb/8/8/R1pP2k1/4P3/P7/K7 b - d3 0 1", 3, 4_135),
            ("4k3/8/8/3pP3/8/8/8/4R1K1 w - d6 0 1", 3, 1_369),
            ("2k5/8/8/8/2b5/8/8/2R1K2R w K - 0 1", 3, 2_527),
            ("4r1k1/8/8/8/8/8/4N3/4K3 w - - 0 1", 3, 651),
            ("4r1k1/8/8/8/1b6/8/8/4K3 w - - 0 1", 3, 274),
            ("1r5k/P7/8/8/8/8/8/7K w - - 0 1", 3, 1_034),
        ];
        for (fen, depth, expected) in cases {
            let mut pos = Position::from_fen(fen).unwrap();
            assert_eq!(perft(&mut pos, depth), expected, "{fen}");
        }
    }

    #[test]
    fn rejects_corrupt_en_passant_state() {
        assert!(Position::from_fen("7k/8/8/P7/8/8/8/7K w - b6 0 1").is_err());
    }

    #[test]
    fn repetition_hash_only_includes_legal_en_passant() {
        let no_ep = Position::from_fen("rnbqkbnr/pppppppp/8/8/P7/8/1PPPPPPP/RNBQKBNR b KQkq - 0 1")
            .unwrap();
        let uncapturable =
            Position::from_fen("rnbqkbnr/pppppppp/8/8/P7/8/1PPPPPPP/RNBQKBNR b KQkq a3 0 1")
                .unwrap();
        assert_eq!(no_ep.hash, uncapturable.hash);

        let legal = Position::from_fen("7k/8/8/8/Pp6/8/8/7K b - a3 0 1").unwrap();
        let missing = Position::from_fen("7k/8/8/8/Pp6/8/8/7K b - - 0 1").unwrap();
        assert_ne!(legal.hash, missing.hash);
    }

    #[test]
    fn draw_material_and_stalemate_are_recognized() {
        for fen in [
            "8/8/8/8/8/8/4k3/7K w - - 0 1",
            "8/8/8/8/8/8/4k3/6BK w - - 0 1",
            "8/8/8/8/8/8/4k3/6NK w - - 0 1",
        ] {
            assert!(insufficient_material(&Position::from_fen(fen).unwrap()));
        }
        let mut stale = Position::from_fen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1").unwrap();
        assert!(!stale.in_check(stale.side));
        assert!(!has_legal_move(&mut stale));
    }

    #[test]
    fn mate_beats_rule_fifty_and_rook_underpromotion_wins() {
        let stop = Arc::new(AtomicBool::new(false));
        let mut searcher = Searcher::new(4, stop);
        let mut mate = Position::from_fen("7k/5Q2/6K1/8/8/8/8/8 w - - 99 1").unwrap();
        let mate_hash = mate.hash;
        let mv = searcher.search(
            &mut mate,
            GoLimits {
                depth: 2,
                soft: None,
                hard: None,
                nodes: None,
            },
            &[mate_hash],
        );
        assert!(["f7g7", "f7h7", "f7e8", "f7f8"].contains(&move_to_uci(mv).as_str()));

        let mut promotion = Position::from_fen("8/1P6/k7/8/1K6/8/8/8 w - - 0 1").unwrap();
        let promotion_hash = promotion.hash;
        let mv = searcher.search(
            &mut promotion,
            GoLimits {
                depth: 3,
                soft: None,
                hard: None,
                nodes: None,
            },
            &[promotion_hash],
        );
        assert_eq!(move_to_uci(mv), "b7b8r");
    }

    #[test]
    fn repetition_requires_three_occurrences() {
        let stop = Arc::new(AtomicBool::new(false));
        let mut searcher = Searcher::new(1, stop);
        let mut pos = Position::from_fen(START_FEN).unwrap();
        let mut history = Vec::new();
        set_position(
            "position startpos moves g1f3 g8f6 f3g1 f6g8",
            &mut pos,
            &mut history,
        )
        .unwrap();
        searcher.hash_len = history.len();
        searcher.hashes[..history.len()].copy_from_slice(&history);
        assert!(!searcher.repetition(&pos));

        set_position(
            "position startpos moves g1f3 g8f6 f3g1 f6g8 g1f3 g8f6 f3g1 f6g8",
            &mut pos,
            &mut history,
        )
        .unwrap();
        searcher.hash_len = history.len();
        searcher.hashes[..history.len()].copy_from_slice(&history);
        assert!(searcher.repetition(&pos));
    }
}
