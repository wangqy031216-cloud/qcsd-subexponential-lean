import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Computability.Encoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QCSD.Defs

namespace Branch3

open QCSD.Defs

/-!
## Part 1: Composable `QCSD_BoolCircuit` Library
Uses only `def`, `lemma`, and `theorem` over existing types (zero custom `structure` or `inductive`).
-/

def evalSingleGate (inp : ℕ → Bool) (vals : List Bool) (g : QCSD_Gate) : Bool :=
  match g.op with
  | QCSD_GateOp.input => inp g.arg1
  | QCSD_GateOp.tt => true
  | QCSD_GateOp.ff => false
  | QCSD_GateOp.neg => !(vals.getD g.arg1 false)
  | QCSD_GateOp.conj => vals.getD g.arg1 false && vals.getD g.arg2 false
  | QCSD_GateOp.disj => vals.getD g.arg1 false || vals.getD g.arg2 false

lemma evalGates_cons (inp : ℕ → Bool) (g : QCSD_Gate) (gs : List QCSD_Gate) (vals : List Bool) :
    QCSD_evalGates inp (g :: gs) vals =
      QCSD_evalGates inp gs (vals ++ [evalSingleGate inp vals g]) := rfl

lemma evalGates_append (inp : ℕ → Bool) (gs1 gs2 : List QCSD_Gate) (vals : List Bool) :
    QCSD_evalGates inp (gs1 ++ gs2) vals =
      QCSD_evalGates inp gs2 (QCSD_evalGates inp gs1 vals) := by
  induction gs1 generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.cons_append, evalGates_cons]
    exact ih _

lemma evalGates_length (inp : ℕ → Bool) (gs : List QCSD_Gate) (vals : List Bool) :
    (QCSD_evalGates inp gs vals).length = vals.length + gs.length := by
  induction gs generalizing vals with
  | nil => simp [QCSD_evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma evalGates_prefix (inp : ℕ → Bool) (gs : List QCSD_Gate) (vals : List Bool) :
    ∃ suf : List Bool, QCSD_evalGates inp gs vals = vals ++ suf := by
  induction gs generalizing vals with
  | nil => exact ⟨[], by simp [QCSD_evalGates]⟩
  | cons g gs ih =>
    rw [evalGates_cons]
    obtain ⟨suf, hsuf⟩ := ih (vals ++ [evalSingleGate inp vals g])
    exact ⟨evalSingleGate inp vals g :: suf, by simpa [List.append_assoc] using hsuf⟩

lemma list_getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma list_getD_singleton (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma evalGates_getD_lt (inp : ℕ → Bool) (gs : List QCSD_Gate) (vals : List Bool)
    (i : ℕ) (hi : i < vals.length) :
    (QCSD_evalGates inp gs vals).getD i false = vals.getD i false := by
  obtain ⟨suf, hsuf⟩ := evalGates_prefix inp gs vals
  rw [hsuf, list_getD_append_left _ _ _ hi]

def wireVal (inp : ℕ → Bool) (gs : List QCSD_Gate) (w : ℕ) : Bool :=
  (QCSD_evalGates inp gs []).getD w false

lemma wireVal_append_left (inp : ℕ → Bool) (gs1 gs2 : List QCSD_Gate)
    (w : ℕ) (hw : w < gs1.length) :
    wireVal inp (gs1 ++ gs2) w = wireVal inp gs1 w := by
  unfold wireVal
  rw [evalGates_append]
  apply evalGates_getD_lt
  rw [evalGates_length]
  simpa using hw

lemma wireVal_snoc (inp : ℕ → Bool) (gs : List QCSD_Gate) (g : QCSD_Gate) :
    wireVal inp (gs ++ [g]) gs.length =
      evalSingleGate inp (QCSD_evalGates inp gs []) g := by
  unfold wireVal
  rw [evalGates_append, evalGates_cons]
  simp only [QCSD_evalGates]
  have hlen : (QCSD_evalGates inp gs []).length = gs.length := by
    simpa using evalGates_length inp gs []
  rw [← hlen, list_getD_singleton]

lemma evalCircuit_eq_wireVal (numIn : ℕ) (gs : List QCSD_Gate) (inp : ℕ → Bool) :
    QCSD_evalCircuit ⟨numIn, gs⟩ inp = wireVal inp gs (gs.length - 1) := rfl

def gateWFAt (numIn pos : ℕ) (g : QCSD_Gate) : Prop :=
  match g.op with
  | QCSD_GateOp.input => g.arg1 < numIn
  | QCSD_GateOp.tt => True
  | QCSD_GateOp.ff => True
  | QCSD_GateOp.neg => g.arg1 < pos
  | QCSD_GateOp.conj => g.arg1 < pos ∧ g.arg2 < pos
  | QCSD_GateOp.disj => g.arg1 < pos ∧ g.arg2 < pos

def gatesWF (numIn off : ℕ) : List QCSD_Gate → Prop
  | [] => True
  | g :: gs => gateWFAt numIn off g ∧ gatesWF numIn (off + 1) gs

lemma gatesWF_append (numIn off : ℕ) (gs1 gs2 : List QCSD_Gate) :
    gatesWF numIn off (gs1 ++ gs2) ↔
      gatesWF numIn off gs1 ∧ gatesWF numIn (off + gs1.length) gs2 := by
  induction gs1 generalizing off with
  | nil => simp [gatesWF]
  | cons g gs ih =>
    simp only [List.cons_append, gatesWF, List.length_cons]
    rw [ih (off + 1)]
    have hadd : off + 1 + gs.length = off + (gs.length + 1) := by omega
    rw [hadd]
    exact and_assoc.symm

lemma gatesWF_get (numIn off : ℕ) (gs : List QCSD_Gate)
    (h : gatesWF numIn off gs) (i : ℕ) (hi : i < gs.length) :
    gateWFAt numIn (off + i) (gs.get ⟨i, hi⟩) := by
  induction gs generalizing off i with
  | nil => cases hi
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := h
    cases i with
    | zero => simpa using hg
    | succ j =>
      have hj : j < gs.length := Nat.lt_of_succ_lt_succ hi
      have := ih (off + 1) hgs j hj
      have hadd : off + 1 + j = off + (j + 1) := by omega
      rwa [hadd] at this

lemma circuitWF_of_gatesWF (numIn : ℕ) (gs : List QCSD_Gate) (h : gatesWF numIn 0 gs) :
    QCSD_circuitWF ⟨numIn, gs⟩ := by
  intro i g hopt
  unfold QCSD_gateAtOpt at hopt
  split_ifs at hopt with hi
  · injection hopt with hg
    subst hg
    have hwf := gatesWF_get numIn 0 gs h i hi
    unfold gateWFAt at hwf
    rw [Nat.zero_add] at hwf
    rcases hget : gs.get ⟨i, hi⟩ with ⟨op, a1, a2⟩
    rw [hget] at hwf
    cases op <;> exact hwf

def gateWFAtB (numIn pos : ℕ) (g : QCSD_Gate) : Bool :=
  match g.op with
  | QCSD_GateOp.input => decide (g.arg1 < numIn)
  | QCSD_GateOp.tt => true
  | QCSD_GateOp.ff => true
  | QCSD_GateOp.neg => decide (g.arg1 < pos)
  | QCSD_GateOp.conj => decide (g.arg1 < pos ∧ g.arg2 < pos)
  | QCSD_GateOp.disj => decide (g.arg1 < pos ∧ g.arg2 < pos)

def gatesWFB (numIn off : ℕ) : List QCSD_Gate → Bool
  | [] => true
  | g :: gs => gateWFAtB numIn off g && gatesWFB numIn (off + 1) gs

lemma gatesWF_of_gatesWFB (numIn : ℕ) :
    ∀ (gs : List QCSD_Gate) (off : ℕ), gatesWFB numIn off gs = true → gatesWF numIn off gs
  | [], _, _ => trivial
  | g :: gs, off, h => by
    simp only [gatesWFB, Bool.and_eq_true] at h
    refine ⟨?_, gatesWF_of_gatesWFB numIn gs (off + 1) h.2⟩
    unfold gateWFAtB at h
    unfold gateWFAt
    cases hop : g.op <;> simp [hop] at h ⊢ <;> exact h.1

/-! ### Primitive Gate Emitters (without `let` in Prop types) -/

def emitConst (gs : List QCSD_Gate) (b : Bool) : List QCSD_Gate × ℕ :=
  (gs ++ [⟨if b then QCSD_GateOp.tt else QCSD_GateOp.ff, 0, 0⟩], gs.length)

def emitInput (gs : List QCSD_Gate) (i : ℕ) : List QCSD_Gate × ℕ :=
  (gs ++ [⟨QCSD_GateOp.input, i, 0⟩], gs.length)

def emitNeg (gs : List QCSD_Gate) (a : ℕ) : List QCSD_Gate × ℕ :=
  (gs ++ [⟨QCSD_GateOp.neg, a, 0⟩], gs.length)

def emitConj (gs : List QCSD_Gate) (a b : ℕ) : List QCSD_Gate × ℕ :=
  (gs ++ [⟨QCSD_GateOp.conj, a, b⟩], gs.length)

def emitDisj (gs : List QCSD_Gate) (a b : ℕ) : List QCSD_Gate × ℕ :=
  (gs ++ [⟨QCSD_GateOp.disj, a, b⟩], gs.length)

def emitXor (gs : List QCSD_Gate) (a b : ℕ) : List QCSD_Gate × ℕ :=
  let o := gs.length
  (gs ++ [⟨QCSD_GateOp.neg, b, 0⟩,
          ⟨QCSD_GateOp.conj, a, o⟩,
          ⟨QCSD_GateOp.neg, a, 0⟩,
          ⟨QCSD_GateOp.conj, o + 2, b⟩,
          ⟨QCSD_GateOp.disj, o + 1, o + 3⟩], o + 4)

def emitEq (gs : List QCSD_Gate) (a b : ℕ) : List QCSD_Gate × ℕ :=
  let r := emitXor gs a b
  emitNeg r.1 r.2

lemma emitConst_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (b : Bool)
    (hwf : gatesWF numIn 0 gs) :
    (emitConst gs b).1.length = gs.length + 1 ∧
    (emitConst gs b).2 = gs.length ∧
    (∃ suf, (emitConst gs b).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitConst gs b).1 ∧
    wireVal inp (emitConst gs b).1 (emitConst gs b).2 = b := by
  unfold emitConst
  refine ⟨by simp, rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [gatesWF_append]
    refine ⟨hwf, ?_⟩
    cases b <;> simp [gatesWF, gateWFAt]
  · rw [wireVal_snoc]
    cases b <;> simp [evalSingleGate]

lemma emitNeg_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (a : ℕ)
    (hwf : gatesWF numIn 0 gs) (ha : a < gs.length) :
    (emitNeg gs a).1.length = gs.length + 1 ∧
    (emitNeg gs a).2 = gs.length ∧
    (∃ suf, (emitNeg gs a).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitNeg gs a).1 ∧
    wireVal inp (emitNeg gs a).1 (emitNeg gs a).2 = !(wireVal inp gs a) := by
  unfold emitNeg
  refine ⟨by simp, rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [gatesWF_append]
    exact ⟨hwf, by simp [gatesWF, gateWFAt, ha]⟩
  · rw [wireVal_snoc]; rfl

lemma emitConj_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (a b : ℕ)
    (hwf : gatesWF numIn 0 gs) (ha : a < gs.length) (hb : b < gs.length) :
    (emitConj gs a b).1.length = gs.length + 1 ∧
    (emitConj gs a b).2 = gs.length ∧
    (∃ suf, (emitConj gs a b).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitConj gs a b).1 ∧
    wireVal inp (emitConj gs a b).1 (emitConj gs a b).2 =
      (wireVal inp gs a && wireVal inp gs b) := by
  unfold emitConj
  refine ⟨by simp, rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [gatesWF_append]
    exact ⟨hwf, by simp [gatesWF, gateWFAt, ha, hb]⟩
  · rw [wireVal_snoc]; rfl

lemma emitDisj_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (a b : ℕ)
    (hwf : gatesWF numIn 0 gs) (ha : a < gs.length) (hb : b < gs.length) :
    (emitDisj gs a b).1.length = gs.length + 1 ∧
    (emitDisj gs a b).2 = gs.length ∧
    (∃ suf, (emitDisj gs a b).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitDisj gs a b).1 ∧
    wireVal inp (emitDisj gs a b).1 (emitDisj gs a b).2 =
      (wireVal inp gs a || wireVal inp gs b) := by
  unfold emitDisj
  refine ⟨by simp, rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [gatesWF_append]
    exact ⟨hwf, by simp [gatesWF, gateWFAt, ha, hb]⟩
  · rw [wireVal_snoc]; rfl

lemma emitXor_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (a b : ℕ)
    (hwf : gatesWF numIn 0 gs) (ha : a < gs.length) (hb : b < gs.length) :
    (emitXor gs a b).1.length = gs.length + 5 ∧
    (emitXor gs a b).2 = gs.length + 4 ∧
    (∃ suf, (emitXor gs a b).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitXor gs a b).1 ∧
    wireVal inp (emitXor gs a b).1 (emitXor gs a b).2 =
      bne (wireVal inp gs a) (wireVal inp gs b) := by
  set g1 : QCSD_Gate := ⟨QCSD_GateOp.neg, b, 0⟩
  set g2 : QCSD_Gate := ⟨QCSD_GateOp.conj, a, gs.length⟩
  set g3 : QCSD_Gate := ⟨QCSD_GateOp.neg, a, 0⟩
  set g4 : QCSD_Gate := ⟨QCSD_GateOp.conj, gs.length + 2, b⟩
  set g5 : QCSD_Gate := ⟨QCSD_GateOp.disj, gs.length + 1, gs.length + 3⟩
  have hfst : (emitXor gs a b).1 = gs ++ [g1, g2, g3, g4, g5] := rfl
  have hsnd : (emitXor gs a b).2 = gs.length + 4 := rfl
  refine ⟨by rw [hfst]; simp, hsnd, ⟨[g1, g2, g3, g4, g5], hfst⟩, ?_, ?_⟩
  · rw [hfst, gatesWF_append]
    refine ⟨hwf, ?_⟩
    simp only [gatesWF, gateWFAt, g1, g2, g3, g4, g5, and_true]
    omega
  · rw [hfst, hsnd]
    have step1 : gs ++ [g1, g2, g3, g4, g5] =
        ((((gs ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4]) ++ [g5] := by simp [List.append_assoc]
    rw [step1]
    set l1 := gs ++ [g1]
    set l2 := l1 ++ [g2]
    set l3 := l2 ++ [g3]
    set l4 := l3 ++ [g4]
    have hl1 : l1.length = gs.length + 1 := by simp [l1]
    have hl2 : l2.length = gs.length + 2 := by simp [l2, hl1]
    have hl3 : l3.length = gs.length + 3 := by simp [l3, hl2]
    have hl4 : l4.length = gs.length + 4 := by simp [l4, hl3]
    rw [← hl4, wireVal_snoc]
    have w_g4 : wireVal inp l4 (gs.length + 3) = (!(wireVal inp gs a) && wireVal inp gs b) := by
      rw [← hl3, wireVal_snoc]
      have wb : wireVal inp l3 b = wireVal inp gs b := by
        have : l3 = gs ++ [g1, g2, g3] := by simp [l3, l2, l1, List.append_assoc]
        rw [this, wireVal_append_left _ _ _ _ hb]
      have wg3 : wireVal inp l3 (gs.length + 2) = !(wireVal inp gs a) := by
        rw [← hl2, wireVal_snoc]
        have wa : wireVal inp l2 a = wireVal inp gs a := by
          have : l2 = gs ++ [g1, g2] := by simp [l2, l1, List.append_assoc]
          rw [this, wireVal_append_left _ _ _ _ ha]
        dsimp only [evalSingleGate, g3]
        exact congrArg Bool.not wa
      dsimp only [evalSingleGate, g4]
      exact congrArg₂ Bool.and wg3 wb
    have w_g2 : wireVal inp l4 (gs.length + 1) = (wireVal inp gs a && !(wireVal inp gs b)) := by
      have : l4 = l2 ++ [g3, g4] := by simp [l4, l3, List.append_assoc]
      rw [this, wireVal_append_left _ _ _ _ (by omega), ← hl1, wireVal_snoc]
      have wa1 : wireVal inp l1 a = wireVal inp gs a :=
        wireVal_append_left inp gs [g1] a ha
      have wg1 : wireVal inp l1 gs.length = !(wireVal inp gs b) := by
        rw [wireVal_snoc]
        rfl
      dsimp only [evalSingleGate, g2]
      exact congrArg₂ Bool.and wa1 wg1
    dsimp only [evalSingleGate, g5]
    have hdisj : ((QCSD_evalGates inp l4 []).getD (gs.length + 1) false ||
                  (QCSD_evalGates inp l4 []).getD (gs.length + 3) false) =
        (wireVal inp l4 (gs.length + 1) || wireVal inp l4 (gs.length + 3)) := rfl
    rw [hdisj, w_g2, w_g4]
    cases wireVal inp gs a <;> cases wireVal inp gs b <;> rfl

lemma emitEq_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (a b : ℕ)
    (hwf : gatesWF numIn 0 gs) (ha : a < gs.length) (hb : b < gs.length) :
    (emitEq gs a b).1.length = gs.length + 6 ∧
    (emitEq gs a b).2 = gs.length + 5 ∧
    (∃ suf, (emitEq gs a b).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitEq gs a b).1 ∧
    wireVal inp (emitEq gs a b).1 (emitEq gs a b).2 =
      (wireVal inp gs a == wireVal inp gs b) := by
  unfold emitEq
  dsimp only
  have sx := emitXor_spec numIn inp gs a b hwf ha hb
  have sx1 := sx.1
  have sx2 := sx.2.1
  have hx : (emitXor gs a b).2 < (emitXor gs a b).1.length := by omega
  have sn := emitNeg_spec numIn inp (emitXor gs a b).1 (emitXor gs a b).2 sx.2.2.2.1 hx
  have sn1 := sn.1
  have sn2 := sn.2.1
  obtain ⟨suf1, hsuf1⟩ := sx.2.2.1
  obtain ⟨suf2, hsuf2⟩ := sn.2.2.1
  refine ⟨by omega, by omega, ⟨suf1 ++ suf2, by rw [hsuf2, hsuf1, List.append_assoc]⟩,
    sn.2.2.2.1, ?_⟩
  rw [sn.2.2.2.2, sx.2.2.2.2]
  cases wireVal inp gs a <;> cases wireVal inp gs b <;> rfl

/-! ### List Parity (`emitXorList`) and List Conjunction (`emitAll`) -/

def emitXorListAux : List QCSD_Gate → ℕ → List ℕ → List QCSD_Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitXor gs acc w
    emitXorListAux r.1 r.2 ws

def emitXorList (gs : List QCSD_Gate) (ws : List ℕ) : List QCSD_Gate × ℕ :=
  let r0 := emitConst gs false
  emitXorListAux r0.1 r0.2 ws

lemma emitXorListAux_spec (numIn : ℕ) (inp : ℕ → Bool) (baseGs : List QCSD_Gate) :
    ∀ (ws : List ℕ) (gs : List QCSD_Gate) (acc : ℕ),
      (∃ suf0, gs = baseGs ++ suf0) →
      gatesWF numIn 0 gs →
      acc < gs.length →
      (∀ w ∈ ws, w < baseGs.length) →
      (emitXorListAux gs acc ws).1.length = gs.length + 5 * ws.length ∧
      (emitXorListAux gs acc ws).2 < (emitXorListAux gs acc ws).1.length ∧
      ((emitXorListAux gs acc ws).2 = (emitXorListAux gs acc ws).1.length - 1 ∨
        (ws = [] ∧ (emitXorListAux gs acc ws).2 = acc)) ∧
      (∃ suf, (emitXorListAux gs acc ws).1 = gs ++ suf) ∧
      gatesWF numIn 0 (emitXorListAux gs acc ws).1 ∧
      wireVal inp (emitXorListAux gs acc ws).1 (emitXorListAux gs acc ws).2 =
        ws.foldl (fun b w => bne b (wireVal inp baseGs w)) (wireVal inp gs acc)
  | [], gs, acc, _, hwf, hacc, _ => by
    dsimp only [emitXorListAux, List.length_nil, List.foldl_nil]
    exact ⟨by omega, hacc, Or.inr ⟨rfl, rfl⟩, ⟨[], by simp⟩, hwf, rfl⟩
  | w :: ws, gs, acc, ⟨suf0, hsuf0⟩, hwf, hacc, hws => by
    simp only [emitXorListAux]
    have hw_base : w < baseGs.length := hws w (by simp)
    have hw_gs : w < gs.length := by rw [hsuf0, List.length_append]; omega
    have sx := emitXor_spec numIn inp gs acc w hwf hacc hw_gs
    obtain ⟨suf1, hsuf1⟩ := sx.2.2.1
    have hrec := emitXorListAux_spec numIn inp baseGs ws (emitXor gs acc w).1 (emitXor gs acc w).2
      ⟨suf0 ++ suf1, by rw [hsuf1, hsuf0, List.append_assoc]⟩
      sx.2.2.2.1 (by omega) (fun u hu => hws u (List.mem_cons_of_mem w hu))
    obtain ⟨suf2, hsuf2⟩ := hrec.2.2.2.1
    refine ⟨by simp only [List.length_cons]; omega, hrec.2.1, ?_,
      ⟨suf1 ++ suf2, by rw [hsuf2, hsuf1, List.append_assoc]⟩,
      hrec.2.2.2.2.1, ?_⟩
    · rcases hrec.2.2.1 with hlast | ⟨hnil, hacc'⟩
      · exact Or.inl hlast
      · subst hnil
        left
        simp only [emitXorListAux] at hacc' ⊢
        omega
    · rw [hrec.2.2.2.2.2, sx.2.2.2.2]
      have hw_val : wireVal inp gs w = wireVal inp baseGs w := by
        rw [hsuf0, wireVal_append_left _ _ _ _ hw_base]
      rw [hw_val]
      rfl

lemma emitXorList_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (ws : List ℕ)
    (hwf : gatesWF numIn 0 gs) (hws : ∀ w ∈ ws, w < gs.length) :
    (emitXorList gs ws).1.length = gs.length + 1 + 5 * ws.length ∧
    (emitXorList gs ws).2 = (emitXorList gs ws).1.length - 1 ∧
    (emitXorList gs ws).2 < (emitXorList gs ws).1.length ∧
    (∃ suf, (emitXorList gs ws).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitXorList gs ws).1 ∧
    wireVal inp (emitXorList gs ws).1 (emitXorList gs ws).2 =
      ws.foldl (fun b w => bne b (wireVal inp gs w)) false := by
  unfold emitXorList
  dsimp only
  have s0 := emitConst_spec numIn inp gs false hwf
  obtain ⟨suf0, hsuf0⟩ := s0.2.2.1
  have srec := emitXorListAux_spec numIn inp gs ws (emitConst gs false).1 (emitConst gs false).2
    ⟨suf0, hsuf0⟩ s0.2.2.2.1 (by omega) hws
  obtain ⟨suf1, hsuf1⟩ := srec.2.2.2.1
  have hend : (emitXorListAux (emitConst gs false).1 (emitConst gs false).2 ws).2 =
      (emitXorListAux (emitConst gs false).1 (emitConst gs false).2 ws).1.length - 1 := by
    rcases srec.2.2.1 with h1 | ⟨hnil, h2⟩
    · exact h1
    · subst hnil; simp only [emitXorListAux] at *; omega
  refine ⟨by omega, hend, srec.2.1, ⟨suf0 ++ suf1, by rw [hsuf1, hsuf0, List.append_assoc]⟩,
    srec.2.2.2.2.1, ?_⟩
  rw [srec.2.2.2.2.2, s0.2.2.2.2]

def emitAllAux : List QCSD_Gate → ℕ → List ℕ → List QCSD_Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitConj gs acc w
    emitAllAux r.1 r.2 ws

def emitAll (gs : List QCSD_Gate) (ws : List ℕ) : List QCSD_Gate × ℕ :=
  let r0 := emitConst gs true
  emitAllAux r0.1 r0.2 ws

lemma emitAllAux_spec (numIn : ℕ) (inp : ℕ → Bool) (baseGs : List QCSD_Gate) :
    ∀ (ws : List ℕ) (gs : List QCSD_Gate) (acc : ℕ),
      (∃ suf0, gs = baseGs ++ suf0) →
      gatesWF numIn 0 gs →
      acc < gs.length →
      (∀ w ∈ ws, w < baseGs.length) →
      (emitAllAux gs acc ws).1.length = gs.length + ws.length ∧
      (emitAllAux gs acc ws).2 < (emitAllAux gs acc ws).1.length ∧
      ((emitAllAux gs acc ws).2 = (emitAllAux gs acc ws).1.length - 1 ∨
        (ws = [] ∧ (emitAllAux gs acc ws).2 = acc)) ∧
      (∃ suf, (emitAllAux gs acc ws).1 = gs ++ suf) ∧
      gatesWF numIn 0 (emitAllAux gs acc ws).1 ∧
      wireVal inp (emitAllAux gs acc ws).1 (emitAllAux gs acc ws).2 =
        ws.foldl (fun b w => b && wireVal inp baseGs w) (wireVal inp gs acc)
  | [], gs, acc, _, hwf, hacc, _ => by
    dsimp only [emitAllAux, List.length_nil, List.foldl_nil]
    exact ⟨by omega, hacc, Or.inr ⟨rfl, rfl⟩, ⟨[], by simp⟩, hwf, rfl⟩
  | w :: ws, gs, acc, ⟨suf0, hsuf0⟩, hwf, hacc, hws => by
    simp only [emitAllAux]
    have hw_base : w < baseGs.length := hws w (by simp)
    have hw_gs : w < gs.length := by rw [hsuf0, List.length_append]; omega
    have sc := emitConj_spec numIn inp gs acc w hwf hacc hw_gs
    obtain ⟨suf1, hsuf1⟩ := sc.2.2.1
    have hrec := emitAllAux_spec numIn inp baseGs ws (emitConj gs acc w).1 (emitConj gs acc w).2
      ⟨suf0 ++ suf1, by rw [hsuf1, hsuf0, List.append_assoc]⟩
      sc.2.2.2.1 (by omega) (fun u hu => hws u (List.mem_cons_of_mem w hu))
    obtain ⟨suf2, hsuf2⟩ := hrec.2.2.2.1
    refine ⟨by simp only [List.length_cons]; omega, hrec.2.1, ?_,
      ⟨suf1 ++ suf2, by rw [hsuf2, hsuf1, List.append_assoc]⟩,
      hrec.2.2.2.2.1, ?_⟩
    · rcases hrec.2.2.1 with hlast | ⟨hnil, hacc'⟩
      · exact Or.inl hlast
      · subst hnil
        left
        simp only [emitAllAux] at hacc' ⊢
        omega
    · rw [hrec.2.2.2.2.2, sc.2.2.2.2]
      have hw_val : wireVal inp gs w = wireVal inp baseGs w := by
        rw [hsuf0, wireVal_append_left _ _ _ _ hw_base]
      rw [hw_val]
      rfl

lemma foldl_and_eq_all {α : Type*} (p : α → Bool) (l : List α) (init : Bool) :
    l.foldl (fun b x => b && p x) init = (init && l.all p) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.all_cons]
    rw [ih]
    cases init <;> cases p x <;> simp

lemma emitAll_spec (numIn : ℕ) (inp : ℕ → Bool) (gs : List QCSD_Gate) (ws : List ℕ)
    (hwf : gatesWF numIn 0 gs) (hws : ∀ w ∈ ws, w < gs.length) :
    (emitAll gs ws).1.length = gs.length + 1 + ws.length ∧
    (emitAll gs ws).2 = (emitAll gs ws).1.length - 1 ∧
    (emitAll gs ws).2 < (emitAll gs ws).1.length ∧
    (∃ suf, (emitAll gs ws).1 = gs ++ suf) ∧
    gatesWF numIn 0 (emitAll gs ws).1 ∧
    wireVal inp (emitAll gs ws).1 (emitAll gs ws).2 =
      ws.all (fun w => wireVal inp gs w) := by
  unfold emitAll
  dsimp only
  have s0 := emitConst_spec numIn inp gs true hwf
  obtain ⟨suf0, hsuf0⟩ := s0.2.2.1
  have srec := emitAllAux_spec numIn inp gs ws (emitConst gs true).1 (emitConst gs true).2
    ⟨suf0, hsuf0⟩ s0.2.2.2.1 (by omega) hws
  obtain ⟨suf1, hsuf1⟩ := srec.2.2.2.1
  have hend : (emitAllAux (emitConst gs true).1 (emitConst gs true).2 ws).2 =
      (emitAllAux (emitConst gs true).1 (emitConst gs true).2 ws).1.length - 1 := by
    rcases srec.2.2.1 with h1 | ⟨hnil, h2⟩
    · exact h1
    · subst hnil; simp only [emitAllAux] at *; omega
  refine ⟨by omega, hend, srec.2.1, ⟨suf0 ++ suf1, by rw [hsuf1, hsuf0, List.append_assoc]⟩,
    srec.2.2.2.2.1, ?_⟩
  rw [srec.2.2.2.2.2, s0.2.2.2.2, foldl_and_eq_all]
  simp

/-! ### Input Preloading (`initInputs`) -/

def initInputs (numIn : ℕ) : List QCSD_Gate :=
  (List.range numIn).map (fun i => ⟨QCSD_GateOp.input, i, 0⟩)

lemma initInputs_length (numIn : ℕ) : (initInputs numIn).length = numIn := by
  simp [initInputs]

lemma initInputs_wf (numIn : ℕ) : gatesWF numIn 0 (initInputs numIn) := by
  suffices ∀ k, k ≤ numIn → gatesWF numIn 0 (initInputs k) from this numIn (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => simp [initInputs, gatesWF]
  | succ m ih =>
    unfold initInputs
    rw [List.range_succ, List.map_append, List.map_singleton, gatesWF_append]
    refine ⟨ih (by omega), ?_⟩
    simp [gatesWF, gateWFAt]
    omega

lemma initInputs_wireVal (numIn : ℕ) (inp : ℕ → Bool) (i : ℕ) (hi : i < numIn) :
    wireVal inp (initInputs numIn) i = inp i := by
  suffices ∀ k, k ≤ numIn → ∀ j < k, wireVal inp (initInputs k) j = inp j from
    this numIn (Nat.le_refl _) i hi
  intro k hk
  induction k with
  | zero => intro j hj; cases hj
  | succ m ih =>
    intro j hj
    have hsplit : initInputs (m + 1) = initInputs m ++ [⟨QCSD_GateOp.input, m, 0⟩] := by
      simp [initInputs, List.range_succ]
    rw [hsplit]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
    · rw [wireVal_append_left _ _ _ _ (by simp [initInputs, hlt])]
      exact ih (by omega) j hlt
    · rw [hjeq]
      have hsnoc := wireVal_snoc inp (initInputs m) ⟨QCSD_GateOp.input, m, 0⟩
      rw [initInputs_length] at hsnoc
      exact hsnoc

/-! ### High-Level Circuit Constructors -/

/-- Constant `true` or `false` circuit on `numIn` inputs. -/
def constCircuit (numIn : ℕ) (b : Bool) : QCSD_BoolCircuit :=
  ⟨numIn, [⟨if b then QCSD_GateOp.tt else QCSD_GateOp.ff, 0, 0⟩]⟩

lemma constCircuit_numInputs (numIn : ℕ) (b : Bool) : (constCircuit numIn b).numInputs = numIn := rfl

lemma constCircuit_wf (numIn : ℕ) (b : Bool) : QCSD_circuitWF (constCircuit numIn b) := by
  apply circuitWF_of_gatesWF
  cases b <;> simp [gatesWF, gateWFAt]

lemma constCircuit_eval (numIn : ℕ) (b : Bool) (inp : ℕ → Bool) :
    QCSD_evalCircuit (constCircuit numIn b) inp = b := by
  cases b <;> rfl

lemma constCircuit_size (numIn : ℕ) (b : Bool) :
    QCSD_circuitSize (constCircuit numIn b) = numIn + 1 := by
  simp [constCircuit, QCSD_circuitSize]

/-- 1-input optional bit-pinning circuit: `none` -> `true`, `some b` -> `inp 0 == b`. -/
def pinBitCircuit : Option Bool → QCSD_BoolCircuit
  | none => constCircuit 1 true
  | some true => ⟨1, [⟨QCSD_GateOp.input, 0, 0⟩]⟩
  | some false => ⟨1, [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.neg, 0, 0⟩]⟩

lemma pinBitCircuit_numInputs (opt : Option Bool) : (pinBitCircuit opt).numInputs = 1 := by
  cases opt with
  | none => rfl
  | some b => cases b <;> rfl

lemma pinBitCircuit_wf (opt : Option Bool) : QCSD_circuitWF (pinBitCircuit opt) := by
  cases opt with
  | none => exact constCircuit_wf 1 true
  | some b =>
    cases b <;> {
      apply circuitWF_of_gatesWF
      simp [gatesWF, gateWFAt]
    }

lemma pinBitCircuit_eval (opt : Option Bool) (inp : ℕ → Bool) :
    QCSD_evalCircuit (pinBitCircuit opt) inp =
      match opt with
      | none => true
      | some b => (inp 0 == b) := by
  cases opt with
  | none => rfl
  | some b =>
    cases b <;> cases h0 : inp 0 <;> simp [pinBitCircuit, QCSD_evalCircuit, QCSD_evalGates, h0]

lemma pinBitCircuit_size (opt : Option Bool) : QCSD_circuitSize (pinBitCircuit opt) ≤ 3 := by
  cases opt with
  | none => simp [pinBitCircuit, constCircuit, QCSD_circuitSize]
  | some b => cases b <;> simp [pinBitCircuit, QCSD_circuitSize]

/-- 1-input guarded bit check: evaluates to `guard && (inp 0 == target)`. -/
def guardedBitCircuit (guard target : Bool) : QCSD_BoolCircuit :=
  if guard then pinBitCircuit (some target) else constCircuit 1 false

lemma guardedBitCircuit_numInputs (guard target : Bool) :
    (guardedBitCircuit guard target).numInputs = 1 := by
  unfold guardedBitCircuit
  split_ifs
  · exact pinBitCircuit_numInputs (some target)
  · rfl

lemma guardedBitCircuit_wf (guard target : Bool) :
    QCSD_circuitWF (guardedBitCircuit guard target) := by
  unfold guardedBitCircuit
  split_ifs
  · exact pinBitCircuit_wf (some target)
  · exact constCircuit_wf 1 false

lemma guardedBitCircuit_eval (guard target : Bool) (inp : ℕ → Bool) :
    QCSD_evalCircuit (guardedBitCircuit guard target) inp = (guard && (inp 0 == target)) := by
  unfold guardedBitCircuit
  cases guard <;> simp [pinBitCircuit_eval, constCircuit_eval]

lemma guardedBitCircuit_size (guard target : Bool) :
    QCSD_circuitSize (guardedBitCircuit guard target) ≤ 3 := by
  unfold guardedBitCircuit
  split_ifs
  · exact pinBitCircuit_size (some target)
  · simp [constCircuit_size]

/-- 3-input syndrome check circuit: `(inp 0 ^^ inp 1 ^^ inp 2) == target`. -/
def synCheckCircuit (target : Bool) : QCSD_BoolCircuit :=
  let gs0 : List QCSD_Gate :=
    [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩]
  let r1 := emitXor gs0 0 1
  let r2 := emitXor r1.1 r1.2 2
  let r3 := emitConst r2.1 target
  let r4 := emitEq r3.1 r2.2 r3.2
  ⟨3, r4.1⟩

lemma synCheckCircuit_numInputs (target : Bool) : (synCheckCircuit target).numInputs = 3 := rfl

lemma evalGates_congr_lt (numIn : ℕ) (inp1 inp2 : ℕ → Bool)
    (hinp : ∀ i < numIn, inp1 i = inp2 i) :
    ∀ (gs : List QCSD_Gate) (off : ℕ) (vals : List Bool),
      gatesWF numIn off gs →
      QCSD_evalGates inp1 gs vals = QCSD_evalGates inp2 gs vals
  | [], _, vals, _ => rfl
  | g :: gs, off, vals, ⟨hg, hgs⟩ => by
    rw [evalGates_cons, evalGates_cons]
    have h1 : evalSingleGate inp1 vals g = evalSingleGate inp2 vals g := by
      unfold evalSingleGate
      unfold gateWFAt at hg
      cases hop : g.op <;> simp only [hop] at hg ⊢
      exact hinp g.arg1 hg
    rw [h1]
    exact evalGates_congr_lt numIn inp1 inp2 hinp gs (off + 1) _ hgs

lemma evalCircuit_congr_lt (c : QCSD_BoolCircuit) (hwf : gatesWF c.numInputs 0 c.gates)
    (inp1 inp2 : ℕ → Bool) (hinp : ∀ i < c.numInputs, inp1 i = inp2 i) :
    QCSD_evalCircuit c inp1 = QCSD_evalCircuit c inp2 := by
  unfold QCSD_evalCircuit
  rw [evalGates_congr_lt c.numInputs inp1 inp2 hinp c.gates 0 [] hwf]

lemma synCheckCircuit_wf_and_eval (target : Bool) (inp : ℕ → Bool) :
    QCSD_circuitWF (synCheckCircuit target) ∧
    QCSD_evalCircuit (synCheckCircuit target) inp =
      (bne (bne (inp 0) (inp 1)) (inp 2) == target) ∧
    QCSD_circuitSize (synCheckCircuit target) ≤ 30 := by
  have hwf : gatesWF 3 0 (synCheckCircuit target).gates := by
    apply gatesWF_of_gatesWFB
    cases target <;> rfl
  refine ⟨circuitWF_of_gatesWF 3 _ hwf, ?_, by cases target <;> decide⟩
  have hcongr : QCSD_evalCircuit (synCheckCircuit target) inp =
      QCSD_evalCircuit (synCheckCircuit target)
        (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else inp 2) := by
    apply evalCircuit_congr_lt _ hwf
    intro i hi
    change i < 3 at hi
    rcases i with _ | _ | _ | i' <;> try rfl
    omega
  rw [hcongr]
  generalize inp 0 = b0, inp 1 = b1, inp 2 = b2
  cases target <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-- 5-input full-adder check circuit:
    inputs `0=a, 1=b, 2=cin, 3=sum_out, 4=cout`. -/
def fullAdderCircuit : QCSD_BoolCircuit :=
  let gs0 : List QCSD_Gate :=
    [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩,
     ⟨QCSD_GateOp.input, 3, 0⟩, ⟨QCSD_GateOp.input, 4, 0⟩]
  let rx1 := emitXor gs0 0 1
  let rsum := emitXor rx1.1 rx1.2 2
  let reqS := emitEq rsum.1 3 rsum.2
  let rab := emitConj reqS.1 0 1
  let rac := emitConj rab.1 0 2
  let rbc := emitConj rac.1 1 2
  let ror1 := emitDisj rbc.1 rac.2 rbc.2
  let rcout := emitDisj ror1.1 rab.2 ror1.2
  let reqC := emitEq rcout.1 4 rcout.2
  let rall := emitConj reqC.1 reqS.2 reqC.2
  ⟨5, rall.1⟩

lemma fullAdderCircuit_numInputs : fullAdderCircuit.numInputs = 5 := rfl

lemma fullAdderCircuit_wf_and_eval (inp : ℕ → Bool) :
    QCSD_circuitWF fullAdderCircuit ∧
    QCSD_evalCircuit fullAdderCircuit inp =
      ((inp 3 == bne (bne (inp 0) (inp 1)) (inp 2)) &&
       (inp 4 == ((inp 0 && inp 1) || ((inp 0 && inp 2) || (inp 1 && inp 2))))) ∧
    QCSD_circuitSize fullAdderCircuit ≤ 40 := by
  have hwf : gatesWF 5 0 fullAdderCircuit.gates := gatesWF_of_gatesWFB 5 _ 0 rfl
  refine ⟨circuitWF_of_gatesWF 5 _ hwf, ?_, by decide⟩
  have hcongr : QCSD_evalCircuit fullAdderCircuit inp =
      QCSD_evalCircuit fullAdderCircuit
        (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else if i = 2 then inp 2
          else if i = 3 then inp 3 else inp 4) := by
    apply evalCircuit_congr_lt _ hwf
    intro i hi
    change i < 5 at hi
    rcases i with _ | _ | _ | _ | _ | i' <;> try rfl
    omega
  rw [hcongr]
  generalize inp 0 = b0, inp 1 = b1, inp 2 = b2, inp 3 = b3, inp 4 = b4
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

/-- 3-input ripple-borrow comparator step:
    inputs `0=sum_b, 1=bin, 2=bout`.
    Checks `bout == (if tBit then (sum_b && bin) else (sum_b || bin))`. -/
def borrowStepCircuit (tBit : Bool) : QCSD_BoolCircuit :=
  let gs0 : List QCSD_Gate :=
    [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩]
  let rstep := if tBit then emitConj gs0 0 1 else emitDisj gs0 0 1
  let req := emitEq rstep.1 2 rstep.2
  ⟨3, req.1⟩

lemma borrowStepCircuit_numInputs (tBit : Bool) : (borrowStepCircuit tBit).numInputs = 3 := rfl

lemma borrowStepCircuit_wf_and_eval (tBit : Bool) (inp : ℕ → Bool) :
    QCSD_circuitWF (borrowStepCircuit tBit) ∧
    QCSD_evalCircuit (borrowStepCircuit tBit) inp =
      (inp 2 == (if tBit then (inp 0 && inp 1) else (inp 0 || inp 1))) ∧
    QCSD_circuitSize (borrowStepCircuit tBit) ≤ 15 := by
  have hwf : gatesWF 3 0 (borrowStepCircuit tBit).gates := by
    apply gatesWF_of_gatesWFB
    cases tBit <;> rfl
  refine ⟨circuitWF_of_gatesWF 3 _ hwf, ?_, by cases tBit <;> decide⟩
  have hcongr : QCSD_evalCircuit (borrowStepCircuit tBit) inp =
      QCSD_evalCircuit (borrowStepCircuit tBit)
        (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else inp 2) := by
    apply evalCircuit_congr_lt _ hwf
    intro i hi
    change i < 3 at hi
    rcases i with _ | _ | _ | i' <;> try rfl
    omega
  rw [hcongr]
  generalize inp 0 = b0, inp 1 = b1, inp 2 = b2
  cases tBit <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-! ### Generic Multi-Output $\mathbb{F}_2$-Linear and Bilinear Map Check Circuits -/

def emitParityChecks : List QCSD_Gate → List (ℕ × List ℕ) → List QCSD_Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, (outW, inWs) :: rest =>
    let rx := emitXorList gs inWs
    let req := emitEq rx.1 outW rx.2
    let rrest := emitParityChecks req.1 rest
    (rrest.1, req.2 :: rrest.2)

lemma emitParityChecks_spec (numIn : ℕ) (inp : ℕ → Bool) (baseGs : List QCSD_Gate) (maxIn : ℕ) :
    ∀ (specs : List (ℕ × List ℕ)) (gs : List QCSD_Gate),
      (∃ suf0, gs = baseGs ++ suf0) →
      gatesWF numIn 0 gs →
      (∀ p ∈ specs, p.1 < baseGs.length ∧ p.2.length ≤ maxIn ∧ ∀ w ∈ p.2, w < baseGs.length) →
      (emitParityChecks gs specs).1.length ≤ gs.length + specs.length * (7 + 5 * maxIn) ∧
      (emitParityChecks gs specs).2.length = specs.length ∧
      (∃ suf, (emitParityChecks gs specs).1 = gs ++ suf) ∧
      gatesWF numIn 0 (emitParityChecks gs specs).1 ∧
      (∀ w ∈ (emitParityChecks gs specs).2, w < (emitParityChecks gs specs).1.length) ∧
      (emitParityChecks gs specs).2.all (fun w => wireVal inp (emitParityChecks gs specs).1 w) =
        specs.all (fun p =>
          wireVal inp baseGs p.1 ==
            p.2.foldl (fun b w => bne b (wireVal inp baseGs w)) false)
  | [], gs, _, hwf, _ => by
    dsimp only [emitParityChecks, List.length_nil]
    exact ⟨by omega, rfl, ⟨[], by simp⟩, hwf, by simp, rfl⟩
  | (outW, inWs) :: rest, gs, ⟨suf0, hsuf0⟩, hwf, hsp => by
    simp only [emitParityChecks]
    have hp0 := hsp (outW, inWs) (by simp)
    have hout_base : outW < baseGs.length := hp0.1
    have hlen_in : inWs.length ≤ maxIn := hp0.2.1
    have hin_base : ∀ w ∈ inWs, w < baseGs.length := hp0.2.2
    have hin_gs : ∀ w ∈ inWs, w < gs.length := by
      intro w hw; have := hin_base w hw; rw [hsuf0, List.length_append]; omega
    have sx := emitXorList_spec numIn inp gs inWs hwf hin_gs
    obtain ⟨suf1, hsuf1⟩ := sx.2.2.2.1
    have hout_rx : outW < (emitXorList gs inWs).1.length := by
      rw [hsuf1, hsuf0]; simp only [List.length_append]; omega
    have seq := emitEq_spec numIn inp (emitXorList gs inWs).1 outW (emitXorList gs inWs).2
      sx.2.2.2.2.1 hout_rx sx.2.2.1
    obtain ⟨suf2, hsuf2⟩ := seq.2.2.1
    have hrec := emitParityChecks_spec numIn inp baseGs maxIn rest
      (emitEq (emitXorList gs inWs).1 outW (emitXorList gs inWs).2).1
      ⟨suf0 ++ suf1 ++ suf2, by rw [hsuf2, hsuf1, hsuf0]; simp [List.append_assoc]⟩
      seq.2.2.2.1 (fun p hp => hsp p (List.mem_cons_of_mem _ hp))
    obtain ⟨suf3, hsuf3⟩ := hrec.2.2.1
    refine ⟨?_, by simp [hrec.2.1],
      ⟨suf1 ++ suf2 ++ suf3, by rw [hsuf3, hsuf2, hsuf1]; simp [List.append_assoc]⟩,
      hrec.2.2.2.1, ?_, ?_⟩
    · have hmul : (rest.length + 1) * (7 + 5 * maxIn) =
          (7 + 5 * maxIn) + rest.length * (7 + 5 * maxIn) := by ring
      simp only [List.length_cons]
      have : 5 * inWs.length ≤ 5 * maxIn := Nat.mul_le_mul_left 5 hlen_in
      omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw'
      · rw [hsuf3, List.length_append]; omega
      · exact hrec.2.2.2.2.1 w hw'
    · simp only [List.all_cons]
      rw [hrec.2.2.2.2.2]
      congr 1
      rw [hsuf3, wireVal_append_left _ _ _ _ (by omega), seq.2.2.2.2, sx.2.2.2.2.2]
      have hw_out : wireVal inp (emitXorList gs inWs).1 outW = wireVal inp baseGs outW := by
        rw [hsuf1, hsuf0, List.append_assoc, wireVal_append_left _ _ _ _ hout_base]
      have hw_fold : inWs.foldl (fun b w => bne b (wireVal inp gs w)) false =
          inWs.foldl (fun b w => bne b (wireVal inp baseGs w)) false := by
        have hcongr : ∀ (l : List ℕ) (init : Bool), (∀ w ∈ l, w < baseGs.length) →
            l.foldl (fun b w => bne b (wireVal inp gs w)) init =
            l.foldl (fun b w => bne b (wireVal inp baseGs w)) init := by
          intro l
          induction l with
          | nil => intro init _; rfl
          | cons u us ih =>
            intro init hl
            simp only [List.foldl_cons]
            have hu : wireVal inp gs u = wireVal inp baseGs u := by
              rw [hsuf0, wireVal_append_left _ _ _ _ (hl u (by simp))]
            rw [hu]
            exact ih _ (fun v hv => hl v (List.mem_cons_of_mem u hv))
        exact hcongr inWs false hin_base
      rw [hw_out, hw_fold]

def linearMapTarget (numIn : ℕ) (mat : ℕ → ℕ → Bool) (inp : ℕ → Bool) (j : ℕ) : Bool :=
  ((List.range numIn).filter (fun i => mat j i)).foldl (fun b i => bne b (inp i)) false

def linearMapCheckCircuit (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) : QCSD_BoolCircuit :=
  let totalIn := numIn + numOut
  let gs0 := initInputs totalIn
  let specs := (List.range numOut).map (fun j =>
    (numIn + j, (List.range numIn).filter (fun i => mat j i)))
  let rpc := emitParityChecks gs0 specs
  let rall := emitAll rpc.1 rpc.2
  ⟨totalIn, rall.1⟩

lemma linearMapCheckCircuit_numInputs (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) :
    (linearMapCheckCircuit numIn numOut mat).numInputs = numIn + numOut := rfl

lemma linearMapCheckCircuit_spec (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) (inp : ℕ → Bool) :
    QCSD_circuitWF (linearMapCheckCircuit numIn numOut mat) ∧
    QCSD_evalCircuit (linearMapCheckCircuit numIn numOut mat) inp =
      (List.range numOut).all (fun j => inp (numIn + j) == linearMapTarget numIn mat inp j) ∧
    QCSD_circuitSize (linearMapCheckCircuit numIn numOut mat) ≤
      2 + 2 * numIn + 10 * numOut + 5 * numOut * numIn := by
  unfold linearMapCheckCircuit
  dsimp only
  set totalIn := numIn + numOut
  set gs0 := initInputs totalIn
  have hwf0 : gatesWF totalIn 0 gs0 := initInputs_wf totalIn
  have hlen0 : gs0.length = totalIn := initInputs_length totalIn
  set specs := (List.range numOut).map (fun j =>
    (numIn + j, (List.range numIn).filter (fun i => mat j i)))
  have hspecs : ∀ p ∈ specs, p.1 < gs0.length ∧ p.2.length ≤ numIn ∧ ∀ w ∈ p.2, w < gs0.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
    have hj' : j < numOut := List.mem_range.mp hj
    refine ⟨by omega, ?_, ?_⟩
    · exact le_trans (List.length_filter_le _ _) (by simp)
    · intro w hw
      have hw' : w < numIn := List.mem_range.mp (List.mem_of_mem_filter hw)
      omega
  have spc := emitParityChecks_spec totalIn inp gs0 numIn specs gs0 ⟨[], by simp⟩ hwf0 hspecs
  have sall := emitAll_spec totalIn inp (emitParityChecks gs0 specs).1
    (emitParityChecks gs0 specs).2 spc.2.2.2.1 spc.2.2.2.2.1
  refine ⟨circuitWF_of_gatesWF totalIn _ sall.2.2.2.2.1, ?_, ?_⟩
  · rw [evalCircuit_eq_wireVal, ← sall.2.1, sall.2.2.2.2.2, spc.2.2.2.2.2]
    rw [Bool.eq_iff_iff, List.all_map, List.all_eq_true, List.all_eq_true]
    constructor <;> intro hall j hj <;> {
      have hj' : j < numOut := List.mem_range.mp hj
      have hout : wireVal inp gs0 (numIn + j) = inp (numIn + j) :=
        initInputs_wireVal totalIn inp (numIn + j) (by omega)
      have hfold : ((List.range numIn).filter (fun i => mat j i)).foldl
          (fun b w => bne b (wireVal inp gs0 w)) false = linearMapTarget numIn mat inp j := by
        unfold linearMapTarget
        have hcongr : ∀ (l : List ℕ) (init : Bool), (∀ w ∈ l, w < totalIn) →
            l.foldl (fun b w => bne b (wireVal inp gs0 w)) init =
            l.foldl (fun b w => bne b (inp w)) init := by
          intro l
          induction l with
          | nil => intro init _; rfl
          | cons u us ih =>
            intro init hl
            simp only [List.foldl_cons]
            rw [initInputs_wireVal totalIn inp u (hl u (by simp))]
            exact ih _ (fun v hv => hl v (List.mem_cons_of_mem u hv))
        apply hcongr
        intro w hw
        have : w < numIn := List.mem_range.mp (List.mem_of_mem_filter hw)
        omega
      have hstep := hall j hj
      dsimp only [Function.comp_apply] at hstep ⊢
      have heq_b : (wireVal inp gs0 (numIn + j) ==
          List.foldl (fun b w => b != wireVal inp gs0 w) false
            (List.filter (fun i => mat j i) (List.range numIn))) =
          (inp (numIn + j) == linearMapTarget numIn mat inp j) :=
        congrArg₂ BEq.beq hout hfold
      first | exact heq_b.symm.trans hstep | exact heq_b.trans hstep
    }
  · dsimp only [QCSD_circuitSize]
    have hs_len : specs.length = numOut := by simp [specs]
    have h1 := spc.1
    have h2 := spc.2.1
    have h3 := sall.1
    rw [hs_len] at h1 h2
    rw [h2] at h3
    have hdist : numOut * (7 + 5 * numIn) = 7 * numOut + 5 * numOut * numIn := by ring
    omega

def emitPairConjs : List QCSD_Gate → List (ℕ × ℕ) → List QCSD_Gate
  | gs, [] => gs
  | gs, (a, b) :: rest =>
    let rc := emitConj gs a b
    emitPairConjs rc.1 rest

lemma emitPairConjs_spec (numIn : ℕ) (inp : ℕ → Bool) (baseGs : List QCSD_Gate) :
    ∀ (pairs : List (ℕ × ℕ)) (gs : List QCSD_Gate),
      (∃ suf0, gs = baseGs ++ suf0) →
      gatesWF numIn 0 gs →
      (∀ p ∈ pairs, p.1 < baseGs.length ∧ p.2 < baseGs.length) →
      (emitPairConjs gs pairs).length = gs.length + pairs.length ∧
      (∃ suf, emitPairConjs gs pairs = gs ++ suf) ∧
      gatesWF numIn 0 (emitPairConjs gs pairs) ∧
      (∀ idx : Fin pairs.length,
        wireVal inp (emitPairConjs gs pairs) (gs.length + idx.val) =
          (wireVal inp baseGs (pairs.get idx).1 && wireVal inp baseGs (pairs.get idx).2))
  | [], gs, _, hwf, _ => by
    dsimp only [emitPairConjs, List.length_nil]
    exact ⟨by omega, ⟨[], by simp⟩, hwf, fun idx => idx.elim0⟩
  | (a, b) :: rest, gs, ⟨suf0, hsuf0⟩, hwf, hpairs => by
    simp only [emitPairConjs]
    have hp0 := hpairs (a, b) (by simp)
    have ha_gs : a < gs.length := by rw [hsuf0, List.length_append]; omega
    have hb_gs : b < gs.length := by rw [hsuf0, List.length_append]; omega
    have sc := emitConj_spec numIn inp gs a b hwf ha_gs hb_gs
    obtain ⟨suf1, hsuf1⟩ := sc.2.2.1
    have hrec := emitPairConjs_spec numIn inp baseGs rest (emitConj gs a b).1
      ⟨suf0 ++ suf1, by rw [hsuf1, hsuf0, List.append_assoc]⟩
      sc.2.2.2.1 (fun p hp => hpairs p (List.mem_cons_of_mem _ hp))
    obtain ⟨suf2, hsuf2⟩ := hrec.2.1
    refine ⟨by simp only [List.length_cons]; omega,
      ⟨suf1 ++ suf2, by rw [hsuf2, hsuf1, List.append_assoc]⟩,
      hrec.2.2.1, ?_⟩
    intro ⟨k, hk⟩
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      have hget0 : ((a, b) :: rest).get ⟨0, hk⟩ = (a, b) := rfl
      rw [hget0, hsuf2, wireVal_append_left _ _ _ _ (by omega)]
      have hidx : gs.length = (emitConj gs a b).2 := rfl
      rw [hidx, sc.2.2.2.2]
      rw [hsuf0, wireVal_append_left _ _ _ _ hp0.1, wireVal_append_left _ _ _ _ hp0.2]
    | succ k' =>
      have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
      have hstep := hrec.2.2.2 ⟨k', hk'⟩
      have hpos : gs.length + (k' + 1) = (emitConj gs a b).1.length + k' := by omega
      rw [hpos]
      exact hstep

def bilinearPairs (n1 n2 : ℕ) : List (ℕ × ℕ) :=
  (List.range (n1 * n2)).map (fun k => (k / n2, n1 + k % n2))

def bilinearMapTarget (n1 n2 : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) (inp : ℕ → Bool) (j : ℕ) : Bool :=
  ((List.range (n1 * n2)).filter (fun k => tensor j (k / n2) (k % n2))).foldl
    (fun b k => bne b (inp (k / n2) && inp (n1 + k % n2))) false

def bilinearMapCheckCircuit (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) : QCSD_BoolCircuit :=
  let totalIn := n1 + n2 + nOut
  let gs0 := initInputs totalIn
  let gs1 := emitPairConjs gs0 (bilinearPairs n1 n2)
  let specs := (List.range nOut).map (fun j =>
    (n1 + n2 + j,
     ((List.range (n1 * n2)).filter (fun k => tensor j (k / n2) (k % n2))).map
       (fun k => totalIn + k)))
  let rpc := emitParityChecks gs1 specs
  let rall := emitAll rpc.1 rpc.2
  ⟨totalIn, rall.1⟩

lemma bilinearMapCheckCircuit_numInputs (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) :
    (bilinearMapCheckCircuit n1 n2 nOut tensor).numInputs = n1 + n2 + nOut := rfl

lemma bilinearMapCheckCircuit_spec (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool)
    (hn2 : 0 < n2) (inp : ℕ → Bool) :
    QCSD_circuitWF (bilinearMapCheckCircuit n1 n2 nOut tensor) ∧
    QCSD_evalCircuit (bilinearMapCheckCircuit n1 n2 nOut tensor) inp =
      (List.range nOut).all (fun j => inp (n1 + n2 + j) == bilinearMapTarget n1 n2 tensor inp j) ∧
    QCSD_circuitSize (bilinearMapCheckCircuit n1 n2 nOut tensor) ≤
      2 + 2 * (n1 + n2) + 10 * nOut + n1 * n2 + 5 * nOut * (n1 * n2) := by
  unfold bilinearMapCheckCircuit
  dsimp only
  set totalIn := n1 + n2 + nOut
  set gs0 := initInputs totalIn
  have hwf0 : gatesWF totalIn 0 gs0 := initInputs_wf totalIn
  have hlen0 : gs0.length = totalIn := initInputs_length totalIn
  set pairs := bilinearPairs n1 n2
  have hpairs_len : pairs.length = n1 * n2 := by simp [pairs, bilinearPairs]
  have hpairs_in : ∀ p ∈ pairs, p.1 < gs0.length ∧ p.2 < gs0.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨k, hk, rfl⟩
    have hk' : k < n1 * n2 := List.mem_range.mp hk
    have hdiv : k / n2 < n1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk')
    have hmod : k % n2 < n2 := Nat.mod_lt k hn2
    omega
  have sp := emitPairConjs_spec totalIn inp gs0 pairs gs0 ⟨[], by simp⟩ hwf0 hpairs_in
  set gs1 := emitPairConjs gs0 pairs
  obtain ⟨suf_p, hsuf_p⟩ := sp.2.1
  set specs := (List.range nOut).map (fun j =>
    (n1 + n2 + j,
     ((List.range (n1 * n2)).filter (fun k => tensor j (k / n2) (k % n2))).map
       (fun k => totalIn + k)))
  have hspecs : ∀ p ∈ specs, p.1 < gs1.length ∧ p.2.length ≤ n1 * n2 ∧ ∀ w ∈ p.2, w < gs1.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
    have hj' : j < nOut := List.mem_range.mp hj
    refine ⟨by omega, ?_, ?_⟩
    · rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    · intro w hw
      rcases List.mem_map.mp hw with ⟨k, hk, rfl⟩
      have hk' : k < n1 * n2 := List.mem_range.mp (List.mem_of_mem_filter hk)
      omega
  have spc := emitParityChecks_spec totalIn inp gs1 (n1 * n2) specs gs1 ⟨[], by simp⟩ sp.2.2.1 hspecs
  have sall := emitAll_spec totalIn inp (emitParityChecks gs1 specs).1
    (emitParityChecks gs1 specs).2 spc.2.2.2.1 spc.2.2.2.2.1
  refine ⟨circuitWF_of_gatesWF totalIn _ sall.2.2.2.2.1, ?_, ?_⟩
  · rw [evalCircuit_eq_wireVal, ← sall.2.1, sall.2.2.2.2.2, spc.2.2.2.2.2]
    rw [Bool.eq_iff_iff, List.all_map, List.all_eq_true, List.all_eq_true]
    constructor <;> intro hall j hj <;> {
      have hj' : j < nOut := List.mem_range.mp hj
      have hout : wireVal inp gs1 (n1 + n2 + j) = inp (n1 + n2 + j) := by
        rw [hsuf_p, wireVal_append_left _ _ _ _ (by omega)]
        exact initInputs_wireVal totalIn inp (n1 + n2 + j) (by omega)
      have hfold : (((List.range (n1 * n2)).filter (fun k => tensor j (k / n2) (k % n2))).map
          (fun k => totalIn + k)).foldl (fun b w => bne b (wireVal inp gs1 w)) false =
          bilinearMapTarget n1 n2 tensor inp j := by
        rw [List.foldl_map]
        unfold bilinearMapTarget
        have hcongr : ∀ (l : List ℕ) (init : Bool), (∀ k ∈ l, k < n1 * n2) →
            l.foldl (fun b k => bne b (wireVal inp gs1 (totalIn + k))) init =
            l.foldl (fun b k => bne b (inp (k / n2) && inp (n1 + k % n2))) init := by
          intro l
          induction l with
          | nil => intro init _; rfl
          | cons k ks ih =>
            intro init hl
            simp only [List.foldl_cons]
            have hk : k < n1 * n2 := hl k (by simp)
            have hk_pairs : k < pairs.length := by omega
            have hpair_val := sp.2.2.2 ⟨k, hk_pairs⟩
            rw [hlen0] at hpair_val
            have hp_get : pairs.get ⟨k, hk_pairs⟩ = (k / n2, n1 + k % n2) := by
              simp [pairs, bilinearPairs]
            rw [hp_get] at hpair_val
            have hdiv : k / n2 < n1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
            have hmod : k % n2 < n2 := Nat.mod_lt k hn2
            rw [hpair_val,
                initInputs_wireVal totalIn inp (k / n2) (by omega),
                initInputs_wireVal totalIn inp (n1 + k % n2) (by omega)]
            exact ih _ (fun v hv => hl v (List.mem_cons_of_mem k hv))
        apply hcongr
        intro k hk
        exact List.mem_range.mp (List.mem_of_mem_filter hk)
      have hstep := hall j hj
      dsimp only [Function.comp_apply] at hstep ⊢
      have heq_b : (wireVal inp gs1 (n1 + n2 + j) ==
          List.foldl (fun b w => b != wireVal inp gs1 w) false
            (List.map (fun k => totalIn + k)
              (List.filter (fun k => tensor j (k / n2) (k % n2)) (List.range (n1 * n2))))) =
          (inp (n1 + n2 + j) == bilinearMapTarget n1 n2 tensor inp j) :=
        congrArg₂ BEq.beq hout hfold
      first | exact heq_b.symm.trans hstep | exact heq_b.trans hstep
    }
  · dsimp only [QCSD_circuitSize]
    have hs_len : specs.length = nOut := by simp [specs]
    have h0 := sp.1
    have h1 := spc.1
    have h2 := spc.2.1
    have h3 := sall.1
    rw [hs_len] at h1 h2
    rw [h2] at h3
    have hdist : nOut * (7 + 5 * (n1 * n2)) = 7 * nOut + 5 * nOut * (n1 * n2) := by ring
    omega

/-!
## Part 2: Powers-of-3 Block & DFT Parameters (§2.1), Quotient-Ring Bit Ops,
## `QCSD_incidentList` Characterization, Contraction Bijection, and `QCSD_TCClass2` Master Bound
-/

def minPowExpAux (b target : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | fuel + 1, acc =>
    if target ≤ b ^ acc then acc else minPowExpAux b target fuel (acc + 1)

def minPowExp (b target : ℕ) : ℕ :=
  minPowExpAux b target target 0

lemma self_le_pow_of_two_le {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := self_le_pow_of_two_le hb n
    have hpos : 1 ≤ b ^ n := Nat.one_le_pow n b (by omega)
    calc
      n + 1 ≤ b ^ n + b ^ n := by omega
      _ = 2 * b ^ n := by ring
      _ ≤ b * b ^ n := Nat.mul_le_mul_right (b ^ n) hb
      _ = b ^ (n + 1) := by rw [pow_succ']

lemma minPowExpAux_spec {b target : ℕ} :
    ∀ (fuel acc : ℕ),
      target ≤ b ^ (acc + fuel) →
      (∀ r < acc, b ^ r < target) →
      target ≤ b ^ minPowExpAux b target fuel acc ∧
        ∀ r < minPowExpAux b target fuel acc, b ^ r < target
  | 0, acc, htop, hlow => by
    simpa [minPowExpAux] using And.intro htop hlow
  | fuel + 1, acc, htop, hlow => by
    simp only [minPowExpAux]
    split_ifs with h
    · exact ⟨h, hlow⟩
    · apply minPowExpAux_spec fuel (acc + 1)
      · have heq : (acc + 1) + fuel = acc + (fuel + 1) := by omega
        simpa [heq] using htop
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
        · exact hlow r hlt
        · exact Nat.lt_of_not_ge h

lemma minPowExp_le_pow {b : ℕ} (hb : 2 ≤ b) (target : ℕ) :
    target ≤ b ^ minPowExp b target :=
  (minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro r hr; omega)).1

lemma lt_of_lt_minPowExp {b : ℕ} (hb : 2 ≤ b) {target r : ℕ}
    (hr : r < minPowExp b target) : b ^ r < target :=
  (minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro x hx; omega)).2 r hr

lemma minPowExp_min {b : ℕ} (hb : 2 ≤ b) {target r : ℕ} (hr : target ≤ b ^ r) :
    minPowExp b target ≤ r := by
  by_contra hgt
  have hlt : b ^ r < target := lt_of_lt_minPowExp hb (Nat.lt_of_not_ge hgt)
  omega

/-- Exact block & 2-layer DFT parameters matching `Branch2Algebra` and §2.1. -/
def paramK (d : ℕ) : ℕ := minPowExp 9 d
def paramJ (d : ℕ) : ℕ := 3 ^ paramK d
def paramM (d : ℕ) : ℕ := (d + paramJ d - 1) / paramJ d
def paramEll (d : ℕ) : ℕ := minPowExp 3 (2 * paramM d - 1)
def paramL (d : ℕ) : ℕ := 3 ^ paramEll d
def paramL1 (d : ℕ) : ℕ := 3 ^ (paramEll d / 2)
def paramL2 (d : ℕ) : ℕ := 3 ^ ((paramEll d + 1) / 2)
def paramOmegaExp (d : ℕ) : ℕ := 3 ^ (paramK d + 1 - paramEll d)
def paramInvOmegaExp (d : ℕ) : ℕ := 3 * paramJ d - paramOmegaExp d

lemma paramJ_sq_eq_nine_pow (d : ℕ) : (paramJ d) ^ 2 = 9 ^ paramK d := by
  unfold paramJ
  calc
    (3 ^ paramK d) ^ 2 = (3 ^ 2) ^ paramK d := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 9 ^ paramK d := by norm_num

lemma one_le_paramJ (d : ℕ) : 1 ≤ paramJ d := Nat.one_le_pow (paramK d) 3 (by decide)
lemma paramJ_pos (d : ℕ) : 0 < paramJ d := one_le_paramJ d

lemma le_paramJ_sq (d : ℕ) : d ≤ (paramJ d) ^ 2 := by
  rw [paramJ_sq_eq_nine_pow]; exact minPowExp_le_pow (by decide) d

lemma paramJ_sq_lt_nine_mul {d : ℕ} (hd : 1 ≤ d) : (paramJ d) ^ 2 < 9 * d := by
  rw [paramJ_sq_eq_nine_pow]
  rcases Nat.eq_zero_or_pos (paramK d) with hk0 | hkpos
  · rw [hk0]; simp only [pow_zero]; omega
  · have hklt : paramK d - 1 < minPowExp 9 d := by unfold paramK at hkpos ⊢; omega
    have hlt : 9 ^ (paramK d - 1) < d :=
      lt_of_lt_minPowExp (b := 9) (by decide) (target := d) hklt
    have hpow : 9 ^ paramK d = 9 * 9 ^ (paramK d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hkpos, pow_succ']
    omega

lemma one_le_paramM {d : ℕ} (hd : 1 ≤ d) : 1 ≤ paramM d := by
  unfold paramM
  exact (Nat.le_div_iff_mul_le (one_le_paramJ d)).2 (by omega)

lemma le_paramM_mul_paramJ (d : ℕ) : d ≤ paramM d * paramJ d := by
  unfold paramM
  have hJ : 0 < paramJ d := paramJ_pos d
  have hdiv := Nat.div_add_mod (d + paramJ d - 1) (paramJ d)
  have hmod : (d + paramJ d - 1) % paramJ d < paramJ d := Nat.mod_lt _ hJ
  have hmul : paramJ d * ((d + paramJ d - 1) / paramJ d) =
      ((d + paramJ d - 1) / paramJ d) * paramJ d := Nat.mul_comm _ _
  omega

lemma paramM_le_paramJ {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ paramJ d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hdJ : d ≤ (paramJ d) ^ 2 := le_paramJ_sq d
  have hlt : d + paramJ d - 1 < (paramJ d + 1) * paramJ d := by
    have hsq : (paramJ d + 1) * paramJ d = (paramJ d) ^ 2 + paramJ d := by ring
    omega
  have hdiv_lt : (d + paramJ d - 1) / paramJ d < paramJ d + 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  omega

lemma one_le_paramL (d : ℕ) : 1 ≤ paramL d := Nat.one_le_pow (paramEll d) 3 (by decide)
lemma one_le_paramL1 (d : ℕ) : 1 ≤ paramL1 d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_paramL2 (d : ℕ) : 1 ≤ paramL2 d := Nat.one_le_pow _ 3 (by decide)

lemma two_mul_paramM_sub_one_le_paramL (d : ℕ) : 2 * paramM d - 1 ≤ paramL d :=
  minPowExp_le_pow (by decide) (2 * paramM d - 1)

lemma paramM_le_paramL {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ paramL d := by
  have hm := one_le_paramM hd
  have hL := two_mul_paramM_sub_one_le_paramL d
  omega

lemma paramEll_le_paramK_succ {d : ℕ} (hd : 1 ≤ d) : paramEll d ≤ paramK d + 1 := by
  apply minPowExp_min (by decide)
  have hm := paramM_le_paramJ hd
  have hJ := one_le_paramJ d
  have hpow : 3 ^ (paramK d + 1) = 3 * paramJ d := by unfold paramJ; rw [pow_succ']
  omega

lemma paramL_le_three_mul_paramJ {d : ℕ} (hd : 1 ≤ d) : paramL d ≤ 3 * paramJ d := by
  calc
    paramL d = 3 ^ paramEll d := rfl
    _ ≤ 3 ^ (paramK d + 1) := Nat.pow_le_pow_right (by decide) (paramEll_le_paramK_succ hd)
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma paramL_mul_omegaExp {d : ℕ} (hd : 1 ≤ d) :
    paramL d * paramOmegaExp d = 3 * paramJ d := by
  unfold paramL paramOmegaExp
  rw [← pow_add, Nat.add_sub_of_le (paramEll_le_paramK_succ hd)]
  unfold paramJ
  rw [pow_succ']

lemma paramL_eq_mul (d : ℕ) : paramL d = paramL1 d * paramL2 d := by
  unfold paramL paramL1 paramL2
  rw [← pow_add]
  congr 1
  omega

lemma paramL1_le_paramL2 (d : ℕ) : paramL1 d ≤ paramL2 d :=
  Nat.pow_le_pow_right (by decide) (by omega)

lemma paramL2_sq_le_nine_mul_paramJ {d : ℕ} (hd : 1 ≤ d) :
    (paramL2 d) ^ 2 ≤ 9 * paramJ d := by
  have hexp : 2 * ((paramEll d + 1) / 2) ≤ paramEll d + 1 := by omega
  calc
    (paramL2 d) ^ 2 = 3 ^ (2 * ((paramEll d + 1) / 2)) := by
      unfold paramL2; rw [← pow_mul, mul_comm]
    _ ≤ 3 ^ (paramEll d + 1) := Nat.pow_le_pow_right (by decide) hexp
    _ = 3 * paramL d := by unfold paramL; rw [pow_succ']
    _ ≤ 3 * (3 * paramJ d) := Nat.mul_le_mul_left 3 (paramL_le_three_mul_paramJ hd)
    _ = 9 * paramJ d := by ring

lemma four_J_L2_pow4_lt {d : ℕ} (hd : 1 ≤ d) :
    (4 * paramJ d * paramL2 d) ^ 4 < 63 ^ 4 * d ^ 3 := by
  set J := paramJ d
  set L2 := paramL2 d
  have hL2 : L2 ^ 2 ≤ 9 * J := paramL2_sq_le_nine_mul_paramJ hd
  have hJ2 : J ^ 2 < 9 * d := paramJ_sq_lt_nine_mul hd
  have hsq : (4 * J * L2) ^ 2 ≤ 144 * J ^ 3 := by
    calc
      (4 * J * L2) ^ 2 = 16 * J ^ 2 * L2 ^ 2 := by ring
      _ ≤ 16 * J ^ 2 * (9 * J) := Nat.mul_le_mul_left _ hL2
      _ = 144 * J ^ 3 := by ring
  have hpow4 : (4 * J * L2) ^ 4 ≤ 20736 * (J ^ 2) ^ 3 := by
    calc
      (4 * J * L2) ^ 4 = ((4 * J * L2) ^ 2) ^ 2 := by ring
      _ ≤ (144 * J ^ 3) ^ 2 := Nat.pow_le_pow_left hsq 2
      _ = 20736 * (J ^ 2) ^ 3 := by ring
  have hJ6 : (J ^ 2) ^ 3 < (9 * d) ^ 3 := Nat.pow_lt_pow_left hJ2 (by decide)
  have hd3 : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
  calc
    (4 * J * L2) ^ 4 ≤ 20736 * (J ^ 2) ^ 3 := hpow4
    _ < 20736 * (9 * d) ^ 3 := (Nat.mul_lt_mul_left (by decide)).2 hJ6
    _ = 15116544 * d ^ 3 := by ring
    _ < 15752961 * d ^ 3 := (Nat.mul_lt_mul_right (by omega)).2 (by decide)
    _ = 63 ^ 4 * d ^ 3 := by norm_num

lemma six_J_pow4_lt {d : ℕ} (hd : 1 ≤ d) :
    (6 * paramJ d) ^ 4 < 63 ^ 4 * d ^ 3 := by
  set J := paramJ d
  have hJ2 : J ^ 2 < 9 * d := paramJ_sq_lt_nine_mul hd
  have hJ4 : (J ^ 2) ^ 2 < (9 * d) ^ 2 := Nat.pow_lt_pow_left hJ2 (by decide)
  have hd23 : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide)
  have hd3 : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
  calc
    (6 * J) ^ 4 = 1296 * (J ^ 2) ^ 2 := by ring
    _ < 1296 * (9 * d) ^ 2 := (Nat.mul_lt_mul_left (by decide)).2 hJ4
    _ = 104976 * d ^ 2 := by ring
    _ ≤ 104976 * d ^ 3 := Nat.mul_le_mul_left _ hd23
    _ < 15752961 * d ^ 3 := (Nat.mul_lt_mul_right (by omega)).2 (by decide)
    _ = 63 ^ 4 * d ^ 3 := by norm_num

/-! ### Quotient-Ring Bit Operations in $\mathbb{F}_2[Y]/(Y^{2J} + Y^J + 1)$ and 2-Layer DFT Spec -/

/-- Coefficient of $Y^p$ ($0 \le p < 2J$) in $Y^m \bmod (Y^{2J} + Y^J + 1)$. -/
def coeffPowY (J m p : ℕ) : Bool :=
  decide (m % (3 * J) = p ∨ m % (3 * J) = 2 * J + p % J)

/-- Bitwise parity of a list of Booleans. -/
def boolListParity (l : List Bool) : Bool :=
  l.foldl bne false

/-- Ring multiplication tensor in $A = \mathbb{F}_2[Y]/(Y^{2J} + Y^J + 1)$. -/
def ringMulTensor (J : ℕ) (p t1 t2 : ℕ) : Bool :=
  coeffPowY J (t1 + t2) p

def ringMulBits (J : ℕ) (u v : ℕ → Bool) (p : ℕ) : Bool :=
  bilinearMapTarget (2 * J) (2 * J) (ringMulTensor J)
    (fun idx => if idx < 2 * J then u idx else v (idx - 2 * J)) p

/-- Forward Stage-1 input wire indices for slice `j2 < L2`:
    all `idx < n` whose block `idx / J` satisfies `(idx / J) % L2 = j2`. -/
def fwdSt1InIndices (n J L2 j2 : ℕ) : List ℕ :=
  (List.range n).filter (fun idx => decide ((idx / J) % L2 = j2))

def fwdSt1Mat (J L1 wExp : ℕ) (inIndices : List ℕ) (outIdx inK : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let idx := inIndices.getD inK 0
  let r := idx / J
  let u := idx % J
  decide (q1 < L1) && coeffPowY J (wExp * r * q1 + u) p

/-- Full Stage-1 matrix (used for inverse DFT Stage 1 where all `2 * J * L1` input bits exist). -/
def fullSt1Mat (J L1 L2 wExp j2 : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j1 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  let r := L2 * j1 + j2
  decide (q1 < L1 ∧ j1 < L1) && coeffPowY J (wExp * r * q1 + t) p

/-- Stage-2 matrix (both forward and inverse): for fixed `q1 < L1`, maps `2 * J * L2` inputs
    `(j2, t)` to `2 * J * L2` outputs `(q2, p)` representing frequency `q1 + L1 * q2`. -/
def st2Mat (J L1 L2 wExp : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q2 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j2 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  decide (q2 < L2 ∧ j2 < L2) && coeffPowY J (wExp * L1 * j2 * q2 + t) p

/-- Deterministic functional evaluation of the entire 2-layer DFT + ring product + overlap + cyclic fold! -/
def twoLayerFwdSt1 (n : ℕ) (x : ℕ → Bool) (j2 q1 p : ℕ) : Bool :=
  let J := paramJ n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let wExp := paramOmegaExp n
  let inList := fwdSt1InIndices n J L2 j2
  linearMapTarget inList.length (fwdSt1Mat J L1 wExp inList)
    (fun k => x (inList.getD k 0)) (q1 * (2 * J) + p)

def twoLayerFwdSt2 (n : ℕ) (y : ℕ → ℕ → ℕ → Bool) (q p : ℕ) : Bool :=
  let J := paramJ n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let wExp := paramOmegaExp n
  let q1 := q % L1
  let q2 := q / L1
  linearMapTarget (2 * J * L2) (st2Mat J L1 L2 wExp)
    (fun inIdx => y (inIdx / (2 * J)) q1 (inIdx % (2 * J))) (q2 * (2 * J) + p)

def twoLayerInvSt1 (n : ℕ) (fc : ℕ → ℕ → Bool) (j2 q1 p : ℕ) : Bool :=
  let J := paramJ n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let invExp := paramInvOmegaExp n
  linearMapTarget (2 * J * L1) (fullSt1Mat J L1 L2 invExp j2)
    (fun inIdx => fc (L2 * (inIdx / (2 * J)) + j2) (inIdx % (2 * J))) (q1 * (2 * J) + p)

def twoLayerInvSt2 (n : ℕ) (yc : ℕ → ℕ → ℕ → Bool) (r p : ℕ) : Bool :=
  let J := paramJ n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let invExp := paramInvOmegaExp n
  let q1 := r % L1
  let q2 := r / L1
  linearMapTarget (2 * J * L2) (st2Mat J L1 L2 invExp)
    (fun inIdx => yc (inIdx / (2 * J)) q1 (inIdx % (2 * J))) (q2 * (2 * J) + p)

def twoLayerPolyMulBit (n : ℕ) (a b : ℕ → Bool) (k : ℕ) : Bool :=
  let J := paramJ n
  let L := paramL n
  let ya := twoLayerFwdSt1 n a
  let fa := twoLayerFwdSt2 n ya
  let yb := twoLayerFwdSt1 n b
  let fb := twoLayerFwdSt2 n yb
  let fc := fun q p => ringMulBits J (fa q) (fb q) p
  let yc := twoLayerInvSt1 n fc
  let craw := twoLayerInvSt2 n yc
  let r := k / J
  let u := k % J
  let lo := if r < L then craw r u else false
  let hi := if 0 < r ∧ r - 1 < L then craw (r - 1) (J + u) else false
  bne lo hi

def zmod2ToBool (z : ZMod 2) : Bool := decide (z = (1 : ZMod 2))
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

lemma boolToZMod2_zmod2ToBool (z : ZMod 2) : boolToZMod2 (zmod2ToBool z) = z := by
  fin_cases z <;> rfl

lemma zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> rfl

lemma boolToZMod2_bne (a b : Bool) :
    boolToZMod2 (bne a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> rfl

def twoLayerCycMul (n : ℕ) (a b : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i =>
    let aB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (a ⟨idx, h⟩) else false
    let bB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (b ⟨idx, h⟩) else false
    boolToZMod2 (bne (twoLayerPolyMulBit n aB bB i.val)
                     (twoLayerPolyMulBit n aB bB (i.val + n)))

/-- Clean interface specification for Branch 2's 2-layer DFT block-convolution theorem (§2–§4.1). -/
def TwoLayerConvSpec (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ZMod 2) (i : Fin n),
    twoLayerCycMul n a b i = QCSD_cycMul n a b i

/-! ### `QCSD_incidentList` Exact Characterization & Contraction Bijection Framework -/

lemma list_eq_of_sorted_same_mem {k : ℕ} :
    ∀ (l1 l2 : List (Fin k)),
      l1.Pairwise (· ≤ ·) →
      l1.Nodup →
      l2.Pairwise (· < ·) →
      (∀ x : Fin k, x ∈ l1 ↔ x ∈ l2) →
      l1 = l2
  | [], [], _, _, _, _ => rfl
  | [], b :: bs, _, _, _, hmem => by
    have : b ∈ ([] : List (Fin k)) := (hmem b).mpr (by simp)
    cases this
  | a :: as, [], _, _, _, hmem => by
    have : a ∈ ([] : List (Fin k)) := (hmem a).mp (by simp)
    cases this
  | a :: as, b :: bs, h1_le, h1_nd, h2_lt, hmem => by
    obtain ⟨ha_le, has_le⟩ := List.pairwise_cons.mp h1_le
    obtain ⟨ha_not_mem, has_nd⟩ := List.nodup_cons.mp h1_nd
    obtain ⟨hb_lt, hbs_lt⟩ := List.pairwise_cons.mp h2_lt
    have hab : a = b := by
      have ha_in : a ∈ b :: bs := (hmem a).mp (by simp)
      have hb_in : b ∈ a :: as := (hmem b).mpr (by simp)
      rcases List.mem_cons.mp ha_in with rfl | ha_bs
      · rfl
      · rcases List.mem_cons.mp hb_in with hba | hb_as
        · exact hba.symm
        · have h1 : b < a := hb_lt a ha_bs
          have h2 : a ≤ b := ha_le b hb_as
          exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl b)
    subst hab
    congr 1
    apply list_eq_of_sorted_same_mem as bs has_le has_nd hbs_lt
    intro x
    have hx_ne : x ∈ as → x ≠ a := fun hx hxa => ha_not_mem (hxa ▸ hx)
    have hx_ne2 : x ∈ bs → x ≠ a := fun hx hxa => ne_of_gt (hb_lt x hx) hxa
    constructor
    · intro hx
      have hxin : x ∈ a :: bs := (hmem x).mp (List.mem_cons_of_mem a hx)
      rcases List.mem_cons.mp hxin with rfl | hxb
      · exact absurd hx ha_not_mem
      · exact hxb
    · intro hx
      have hxin : x ∈ a :: as := (hmem x).mpr (List.mem_cons_of_mem a hx)
      rcases List.mem_cons.mp hxin with rfl | hxa
      · exact absurd rfl (hx_ne2 hx)
      · exact hxa

lemma incidentList_eq_of_strictMono (m k : ℕ) (ends : Fin k → Fin m × Fin m)
    (v : Fin m) (l : List (Fin k))
    (h_lt : l.Pairwise (· < ·))
    (h_mem : ∀ e : Fin k, e ∈ l ↔ ((ends e).1 = v ∨ (ends e).2 = v)) :
    QCSD_incidentList m k ends v = l := by
  unfold QCSD_incidentList
  set s := Finset.univ.filter (fun e : Fin k => (ends e).1 = v ∨ (ends e).2 = v)
  apply list_eq_of_sorted_same_mem (s.sort (· ≤ ·)) l
    (s.pairwise_sort (· ≤ ·)) (s.sort_nodup (· ≤ ·)) h_lt
  intro e
  rw [Finset.mem_sort, Finset.mem_filter]
  simp [h_mem e]

def vertexInp (N : QCSD_BoolTensorNetwork2) (v : Fin N.m) (x : Fin N.k → Bool) : ℕ → Bool :=
  fun i =>
    if h : i < (QCSD_incidentList N.m N.k N.ends v).length
    then x ((QCSD_incidentList N.m N.k N.ends v).get ⟨i, h⟩)
    else false

def vertexSat (N : QCSD_BoolTensorNetwork2) (v : Fin N.m) (x : Fin N.k → Bool) : Bool :=
  QCSD_evalCircuit (N.pred v) (vertexInp N v x)

lemma contraction2_eq_card_sat (N : QCSD_BoolTensorNetwork2) :
    QCSD_contraction2 N =
      (Finset.univ.filter (fun x : Fin N.k → Bool => ∀ v : Fin N.m, vertexSat N v x = true)).card := by
  unfold QCSD_contraction2
  have hterm : ∀ x : Fin N.k → Bool,
      (Finset.prod Finset.univ (fun v : Fin N.m =>
        if vertexSat N v x then (1 : ℕ) else 0)) =
      if (∀ v : Fin N.m, vertexSat N v x = true) then 1 else 0 := by
    intro x
    split_ifs with hall
    · apply Finset.prod_eq_one
      intro v _
      simp [hall v]
    · obtain ⟨v, hv⟩ := Classical.not_forall.mp hall
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      cases hsat : vertexSat N v x
      · rfl
      · exact absurd hsat hv
  have hsum : Finset.sum Finset.univ (fun x : Fin N.k → Bool =>
      Finset.prod Finset.univ (fun v : Fin N.m =>
        if QCSD_evalCircuit (N.pred v) (vertexInp N v x) then (1 : ℕ) else 0)) =
      Finset.sum Finset.univ (fun x : Fin N.k → Bool =>
        if (∀ v : Fin N.m, vertexSat N v x = true) then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    exact hterm x
  change Finset.sum Finset.univ (fun x : Fin N.k → Bool =>
      Finset.prod Finset.univ (fun v : Fin N.m =>
        if QCSD_evalCircuit (N.pred v) (vertexInp N v x) then (1 : ℕ) else 0)) = _
  rw [hsum, ← Finset.sum_filter]
  simp

lemma contraction2_eq_card_validIface (N : QCSD_BoolTensorNetwork2) (nIface : ℕ)
    (hle : nIface ≤ N.k)
    (ext : (Fin nIface → Bool) → (Fin N.k → Bool))
    (valid : (Fin nIface → Bool) → Prop) [DecidablePred valid]
    (hext_iface : ∀ (w : Fin nIface → Bool) (i : Fin nIface),
      ext w ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = w i)
    (hchar : ∀ x : Fin N.k → Bool,
      (∀ v : Fin N.m, vertexSat N v x = true) ↔ (∃ w : Fin nIface → Bool, valid w ∧ x = ext w)) :
    QCSD_contraction2 N = (Finset.univ.filter valid).card := by
  rw [contraction2_eq_card_sat]
  symm
  apply Finset.card_bij (fun (w : Fin nIface → Bool) _ => ext w)
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, (hchar (ext w)).mpr ⟨w, hw.2, rfl⟩⟩
  · intro w1 _ w2 _ heq
    funext i
    have h1 := hext_iface w1 i
    have h2 := hext_iface w2 i
    rw [← h1, ← h2, heq]
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨w, hw, rfl⟩ := (hchar x).mp hx.2
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩

/-! ### Master `QCSD_netCost2` and `QCSD_TCClass2` Polynomial Bound Lemma -/

lemma natToUnary_length (m : ℕ) : (QCSD_natToUnary m).length = m + 1 := by
  simp [QCSD_natToUnary]

lemma flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha : (f a).length ≤ B := h a (by simp)
    have has : (as.flatMap f).length ≤ as.length * B :=
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have hmul : (as.length + 1) * B = B + as.length * B := by ring
    omega

lemma encodeGate_length_le_of_wf (c : QCSD_BoolCircuit) (hwf : QCSD_circuitWF c)
    (g : QCSD_Gate) (hg : g ∈ c.gates) :
    (QCSD_encodeGate g).length ≤ 5 + 2 * QCSD_circuitSize c := by
  obtain ⟨idx, rfl⟩ := List.mem_iff_get.mp hg
  have hopt : QCSD_gateAtOpt c.gates idx.val = some (c.gates.get idx) := by
    simp [QCSD_gateAtOpt, idx.isLt]
  have hgate := hwf idx.val (c.gates.get idx) hopt
  have hidx_lt : idx.val < c.gates.length := idx.isLt
  unfold QCSD_encodeGate QCSD_circuitSize
  cases hop : (c.gates.get idx).op <;>
    simp only [hop, QCSD_gateTag, List.length_append, List.length_cons, List.length_nil,
               natToUnary_length] at hgate ⊢ <;>
    omega

lemma encodeCircuit_length_le (c : QCSD_BoolCircuit) (hwf : QCSD_circuitWF c) :
    (QCSD_encodeCircuit c).length ≤ 9 * (QCSD_circuitSize c + 1) ^ 2 := by
  unfold QCSD_encodeCircuit
  simp only [List.length_append, natToUnary_length]
  have hflat : (c.gates.flatMap QCSD_encodeGate).length ≤
      c.gates.length * (5 + 2 * QCSD_circuitSize c) :=
    flatMap_length_le c.gates QCSD_encodeGate _ (encodeGate_length_le_of_wf c hwf)
  set sz := QCSD_circuitSize c
  have h1 : c.numInputs + c.gates.length = sz := rfl
  have h2 : c.gates.length ≤ sz := by omega
  have h3 : c.gates.length * (5 + 2 * sz) ≤ sz * (5 + 2 * sz) :=
    Nat.mul_le_mul_right _ h2
  have h4 : 9 * (sz + 1) ^ 2 = 9 * sz ^ 2 + 18 * sz + 9 := by ring
  have h5 : sz * (5 + 2 * sz) = 2 * sz ^ 2 + 5 * sz := by ring
  omega

lemma netCost2_le_of_bounds (N : QCSD_BoolTensorNetwork2) (Km Kpred : ℕ)
    (hS : 1 ≤ QCSD_edgeCount2 N)
    (hm : N.m ≤ Km * QCSD_edgeCount2 N)
    (hpred : ∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ Kpred * (QCSD_edgeCount2 N) ^ 2) :
    QCSD_netCost2 N ≤
      (5 + 3 * Km + 9 * Km * (Kpred + 1) ^ 2) * (QCSD_edgeCount2 N) ^ 5 := by
  set S := QCSD_edgeCount2 N
  have hk_eq : N.k = S := rfl
  unfold QCSD_netCost2 QCSD_encodeNet2
  simp only [List.length_append, natToUnary_length]
  have hends : ((List.finRange N.k).flatMap (fun e =>
      QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val)).length ≤
      S * (2 * N.m + 2) := by
    have := flatMap_length_le (List.finRange N.k)
      (fun e => QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val)
      (2 * N.m + 2)
      (fun e _ => by
        simp only [List.length_append, natToUnary_length]
        have h1 := (N.ends e).1.isLt
        have h2 := (N.ends e).2.isLt
        omega)
    simpa [List.length_finRange, hk_eq] using this
  have hpreds : ((List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v))).length ≤
      N.m * (9 * ((Kpred + 1) * S ^ 2) ^ 2) := by
    have := flatMap_length_le (List.finRange N.m)
      (fun v => QCSD_encodeCircuit (N.pred v))
      (9 * ((Kpred + 1) * S ^ 2) ^ 2)
      (fun v _ => by
        have hc := encodeCircuit_length_le (N.pred v) (N.wf v)
        have hp := hpred v
        have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow 2 S hS
        have hle1 : QCSD_circuitSize (N.pred v) + 1 ≤ (Kpred + 1) * S ^ 2 := by
          have : (Kpred + 1) * S ^ 2 = Kpred * S ^ 2 + S ^ 2 := by ring
          omega
        exact le_trans hc (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left hle1 2)))
    simpa [List.length_finRange] using this
  have hS15 : S ^ 1 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have hS25 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have hm_cost : N.m * (9 * ((Kpred + 1) * S ^ 2) ^ 2) ≤
      9 * Km * (Kpred + 1) ^ 2 * S ^ 5 := by
    calc
      N.m * (9 * ((Kpred + 1) * S ^ 2) ^ 2)
          ≤ (Km * S) * (9 * ((Kpred + 1) * S ^ 2) ^ 2) := Nat.mul_le_mul_right _ hm
      _ = 9 * Km * (Kpred + 1) ^ 2 * S ^ 5 := by ring
  have hends_cost : S * (2 * N.m + 2) ≤ (2 * Km + 2) * S ^ 2 := by
    calc
      S * (2 * N.m + 2) ≤ S * (2 * (Km * S) + 2) := by
        apply Nat.mul_le_mul_left
        omega
      _ = 2 * Km * S ^ 2 + 2 * S := by ring
      _ ≤ 2 * Km * S ^ 2 + 2 * S ^ 2 := by
        have : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 2 by decide)
        omega
      _ = (2 * Km + 2) * S ^ 2 := by ring
  have hends_cost5 : (2 * Km + 2) * S ^ 2 ≤ (2 * Km + 2) * S ^ 5 :=
    Nat.mul_le_mul_left _ hS25
  have hm1 : N.m + 1 + (N.k + 1) ≤ (Km + 3) * S ^ 5 := by
    have hS_le_S5 : S ≤ S ^ 5 := by simpa using hS15
    have hS5 : 1 ≤ S ^ 5 := Nat.one_le_pow 5 S hS
    have hkm : Km * S ≤ Km * S ^ 5 := Nat.mul_le_mul_left Km hS_le_S5
    have hstep1 : N.m + 1 + (N.k + 1) ≤ Km * S + (S + 2) := by omega
    have hstep2 : Km * S + (S + 2) ≤ Km * S ^ 5 + 3 * S ^ 5 :=
      Nat.add_le_add hkm (by omega)
    have hstep3 : Km * S ^ 5 + 3 * S ^ 5 = (Km + 3) * S ^ 5 := by ring
    exact hstep3 ▸ le_trans hstep1 hstep2
  calc
    N.m + 1 + (N.k + 1) +
        ((List.finRange N.k).flatMap (fun e =>
          QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val)).length +
        ((List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v))).length
      ≤ (Km + 3) * S ^ 5 + (2 * Km + 2) * S ^ 5 + 9 * Km * (Kpred + 1) ^ 2 * S ^ 5 := by
        have he5 : S * (2 * N.m + 2) ≤ (2 * Km + 2) * S ^ 5 := le_trans hends_cost hends_cost5
        omega
    _ = (5 + 3 * Km + 9 * Km * (Kpred + 1) ^ 2) * S ^ 5 := by ring

lemma le_of_pow40_le_real {x y : ℝ} (hy : 0 ≤ y) (hpow : x ^ 40 ≤ y ^ 40) : x ≤ y := by
  by_contra hgt
  have hlt : y < x := lt_of_not_ge hgt
  have : y ^ 40 < x ^ 40 := pow_lt_pow_left₀ hlt hy (by decide)
  linarith

lemma maxDeg2_rpow_bound (N : QCSD_BoolTensorNetwork2)
    (hS : 2 ≤ QCSD_edgeCount2 N)
    (hdeg : ∀ v : Fin N.m, (QCSD_deg2 N v) ^ 4 ≤ 63 ^ 4 * (QCSD_edgeCount2 N) ^ 3) :
    (QCSD_maxDeg2 N : ℝ) ≤ 63 * (QCSD_edgeCount2 N : ℝ) ^ ((9 : ℝ) / 10) := by
  set S := QCSD_edgeCount2 N
  have hmax : QCSD_maxDeg2 N ^ 4 ≤ 63 ^ 4 * S ^ 3 := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin N.m)) with hemp | hne
    · have hm0 : QCSD_maxDeg2 N = 0 := by unfold QCSD_maxDeg2; rw [hemp]; simp
      rw [hm0]; simp
    · obtain ⟨v0, _, hv0⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun v => QCSD_deg2 N v)
      change (Finset.univ.sup fun v => QCSD_deg2 N v) ^ 4 ≤ _
      rw [hv0]
      exact hdeg v0
  have hpow40_nat : (QCSD_maxDeg2 N) ^ 40 ≤ 63 ^ 40 * S ^ 36 := by
    have hp10 : ((QCSD_maxDeg2 N) ^ 4) ^ 10 ≤ (63 ^ 4 * S ^ 3) ^ 10 :=
      Nat.pow_le_pow_left hmax 10
    have hS30_36 : S ^ 30 ≤ S ^ 36 := Nat.pow_le_pow_right (by omega) (by decide)
    calc
      (QCSD_maxDeg2 N) ^ 40 = ((QCSD_maxDeg2 N) ^ 4) ^ 10 := by ring
      _ ≤ (63 ^ 4 * S ^ 3) ^ 10 := hp10
      _ = 63 ^ 40 * S ^ 30 := by ring
      _ ≤ 63 ^ 40 * S ^ 36 := Nat.mul_le_mul_left _ hS30_36
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hrhs_nn : (0 : ℝ) ≤ 63 * (S : ℝ) ^ ((9 : ℝ) / 10) := by
    apply mul_nonneg (by norm_num)
    exact Real.rpow_nonneg hS0 _
  apply le_of_pow40_le_real hrhs_nn
  have hrhs40 : (63 * (S : ℝ) ^ ((9 : ℝ) / 10)) ^ 40 = ((63 ^ 40 * S ^ 36 : ℕ) : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((S : ℝ) ^ ((9 : ℝ) / 10)) 40, ← Real.rpow_mul hS0]
    have hexp : ((9 : ℝ) / 10) * ((40 : ℕ) : ℝ) = ((36 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
    push_cast
    ring
  rw [hrhs40]
  have hcast : (((QCSD_maxDeg2 N) ^ 40 : ℕ) : ℝ) ≤ ((63 ^ 40 * S ^ 36 : ℕ) : ℝ) := by
    exact_mod_cast hpow40_nat
  simpa only [Nat.cast_pow] using hcast

lemma tcClass2_of_bounds (N : QCSD_BoolTensorNetwork2) (Km Kpred : ℕ)
    (hS : 2 ≤ QCSD_edgeCount2 N)
    (hdeg : ∀ v : Fin N.m, (QCSD_deg2 N v) ^ 4 ≤ 63 ^ 4 * (QCSD_edgeCount2 N) ^ 3)
    (hm : N.m ≤ Km * QCSD_edgeCount2 N)
    (hpred : ∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ Kpred * (QCSD_edgeCount2 N) ^ 2) :
    QCSD_TCClass2 63 1 Km 5 (5 + 3 * Km + 9 * Km * (Kpred + 1) ^ 2) 2 Kpred N := by
  refine ⟨hS, maxDeg2_rpow_bound N hS hdeg, ?_, ?_, hpred⟩
  · simpa using hm
  · exact netCost2_le_of_bounds N Km Kpred (by omega) hm hpred

/-!
## Part 3: Section 4.2 Linear-Size Balanced Binary Carry-Ripple Adder Tree & Comparators
-/

def treeLog (N_bits : ℕ) : ℕ := max 1 (minPowExp 2 N_bits)
def treeM (N_bits : ℕ) : ℕ := 2 ^ treeLog N_bits

lemma one_le_treeLog (N_bits : ℕ) : 1 ≤ treeLog N_bits := le_max_left 1 _

lemma treeLog_eq_minPowExp {N_bits : ℕ} (hN : 2 ≤ N_bits) :
    treeLog N_bits = minPowExp 2 N_bits := by
  unfold treeLog
  apply max_eq_right
  by_contra hlt
  have h0 : minPowExp 2 N_bits = 0 := by omega
  have hle : N_bits ≤ 2 ^ minPowExp 2 N_bits := minPowExp_le_pow (by decide) N_bits
  rw [h0] at hle
  omega

lemma le_treeM (N_bits : ℕ) : N_bits ≤ treeM N_bits := by
  unfold treeM treeLog
  exact le_trans (minPowExp_le_pow (by decide) N_bits)
    (Nat.pow_le_pow_right (by decide) (le_max_right 1 _))

lemma treeM_lt_two_mul {N_bits : ℕ} (hN : 2 ≤ N_bits) : treeM N_bits < 2 * N_bits := by
  unfold treeM
  rw [treeLog_eq_minPowExp hN]
  have h1 : 1 ≤ minPowExp 2 N_bits := by
    rw [← treeLog_eq_minPowExp hN]
    exact one_le_treeLog N_bits
  have hlt : 2 ^ (minPowExp 2 N_bits - 1) < N_bits :=
    lt_of_lt_minPowExp (b := 2) (by decide) (target := N_bits) (by omega)
  have hpow : 2 ^ minPowExp 2 N_bits = 2 * 2 ^ (minPowExp 2 N_bits - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ']
  omega

lemma treeLog_le_self {N_bits : ℕ} (hN : 2 ≤ N_bits) : treeLog N_bits ≤ N_bits := by
  have h1 : 1 ≤ treeLog N_bits := one_le_treeLog N_bits
  have hm : treeM N_bits < 2 * N_bits := treeM_lt_two_mul hN
  unfold treeM at hm
  have hpow : 2 ^ (treeLog N_bits - 1) < N_bits := by
    have : 2 ^ treeLog N_bits = 2 * 2 ^ (treeLog N_bits - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ']
    omega
  have hself : treeLog N_bits - 1 ≤ 2 ^ (treeLog N_bits - 1) :=
    self_le_pow_of_two_le (by decide) _
  omega

/-- Unsigned binary integer value of bits `0 .. w - 1` of `f`. -/
def bitsVal : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | w + 1, f => bitsVal w f + (if f w then 1 else 0) * 2 ^ w

lemma bitsVal_congr {w : ℕ} {f g : ℕ → Bool} (h : ∀ b < w, f b = g b) :
    bitsVal w f = bitsVal w g := by
  induction w with
  | zero => rfl
  | succ m ih =>
    simp only [bitsVal]
    rw [ih (fun b hb => h b (by omega)), h m (by omega)]

lemma bitsVal_lt_pow (w : ℕ) (f : ℕ → Bool) : bitsVal w f < 2 ^ w := by
  induction w with
  | zero => simp [bitsVal]
  | succ m ih =>
    simp only [bitsVal]
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ']; ring
    cases f m <;> simp <;> omega

lemma bitsVal_testBit (t : ℕ) : ∀ w : ℕ, bitsVal w (fun b => t.testBit b) = t % 2 ^ w
  | 0 => by simp [bitsVal, Nat.mod_one]
  | w + 1 => by
    simp only [bitsVal, bitsVal_testBit t w]
    have hmod : t % 2 ^ (w + 1) = t % 2 ^ w + 2 ^ w * ((t / 2 ^ w) % 2) :=
      Nat.mod_pow_succ
    have htb : (if t.testBit w then 1 else 0) = (t / 2 ^ w) % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hlt : (t / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by decide)
      rcases Nat.eq_zero_or_pos ((t / 2 ^ w) % 2) with h0 | hpos
      · simp [h0]
      · have h1 : (t / 2 ^ w) % 2 = 1 := by omega
        simp [h1]
    rw [htb, hmod]
    ring

lemma bitsVal_inj {w : ℕ} {f g : ℕ → Bool} (heq : bitsVal w f = bitsVal w g) :
    ∀ b < w, f b = g b := by
  induction w with
  | zero => intro b hb; omega
  | succ m ih =>
    simp only [bitsVal] at heq
    have hlt_f : bitsVal m f < 2 ^ m := bitsVal_lt_pow m f
    have hlt_g : bitsVal m g < 2 ^ m := bitsVal_lt_pow m g
    have htop : f m = g m := by
      cases hf : f m <;> cases hg : g m <;> simp [hf, hg] at heq <;> try rfl
      · omega
      · omega
    have hlow : bitsVal m f = bitsVal m g := by
      rw [htop] at heq
      omega
    intro b hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
    · exact ih hlow b hlt
    · exact htop

lemma bitsVal_eq_iff_testBit (W : ℕ) (f : ℕ → Bool) (t : ℕ) :
    bitsVal W f = t ↔ (t < 2 ^ W ∧ ∀ b < W, f b = t.testBit b) := by
  constructor
  · intro heq
    subst heq
    refine ⟨bitsVal_lt_pow W f, ?_⟩
    apply bitsVal_inj
    rw [bitsVal_testBit, Nat.mod_eq_of_lt (bitsVal_lt_pow W f)]
  · rintro ⟨hlt, hbits⟩
    rw [bitsVal_congr hbits, bitsVal_testBit, Nat.mod_eq_of_lt hlt]

/-- Ripple-carry adder pure bit functions. -/
def rippleCarry (A B : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | b + 1 =>
    (A b && B b) || ((A b && rippleCarry A B b) || (B b && rippleCarry A B b))

def rippleSum (j : ℕ) (A B : ℕ → Bool) (b : ℕ) : Bool :=
  if b < j then bne (bne (A b) (B b)) (rippleCarry A B b)
  else if b = j then rippleCarry A B j
  else false

lemma fullAdder_arith_step (a b c : Bool) :
    (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) =
      (if bne (bne a b) c then 1 else 0) +
        2 * (if (a && b) || ((a && c) || (b && c)) then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma rippleCarry_invariant (A B : ℕ → Bool) :
    ∀ b : ℕ,
      bitsVal b (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) +
        (if rippleCarry A B b then 1 else 0) * 2 ^ b =
      bitsVal b A + bitsVal b B
  | 0 => by simp [bitsVal, rippleCarry]
  | b + 1 => by
    simp only [bitsVal, rippleCarry]
    have ih := rippleCarry_invariant A B b
    have hfa := fullAdder_arith_step (A b) (B b) (rippleCarry A B b)
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ']
    set sa := if A b then 1 else 0
    set sb := if B b then 1 else 0
    set sc := if rippleCarry A B b then 1 else 0
    set ssum := if bne (bne (A b) (B b)) (rippleCarry A B b) then 1 else 0
    set scout := if (A b && B b) || ((A b && rippleCarry A B b) || (B b && rippleCarry A B b)) then 1 else 0
    have hmul : (sa + sb + sc) * 2 ^ b = (ssum + 2 * scout) * 2 ^ b :=
      congrArg (· * 2 ^ b) hfa
    calc
      bitsVal b (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) +
          ssum * 2 ^ b + scout * 2 ^ (b + 1)
        = bitsVal b (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) +
            (ssum + 2 * scout) * 2 ^ b := by rw [hpow]; ring
      _ = bitsVal b (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) +
            (sa + sb + sc) * 2 ^ b := by rw [← hmul]
      _ = (bitsVal b (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) + sc * 2 ^ b) +
            sa * 2 ^ b + sb * 2 ^ b := by ring
      _ = (bitsVal b A + bitsVal b B) + sa * 2 ^ b + sb * 2 ^ b := by rw [ih]
      _ = (bitsVal b A + sa * 2 ^ b) + (bitsVal b B + sb * 2 ^ b) := by ring

lemma rippleSum_val (j : ℕ) (A B : ℕ → Bool) :
    bitsVal (j + 1) (rippleSum j A B) = bitsVal j A + bitsVal j B := by
  simp only [bitsVal]
  have hlow : bitsVal j (rippleSum j A B) =
      bitsVal j (fun k => bne (bne (A k) (B k)) (rippleCarry A B k)) := by
    apply bitsVal_congr
    intro k hk
    simp [rippleSum, hk]
  have htop : rippleSum j A B j = rippleCarry A B j := by simp [rippleSum]
  rw [hlow, htop]
  exact rippleCarry_invariant A B j

/-- Balanced binary adder tree pure level bit functions. -/
def treeLevelBits (N_bits : ℕ) (leaf : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, node, b => decide (node < N_bits ∧ b = 0) && leaf node
  | j + 1, node, b =>
    rippleSum (j + 1) (treeLevelBits N_bits leaf j (2 * node))
                      (treeLevelBits N_bits leaf j (2 * node + 1)) b

lemma sum_range_pair (f : ℕ → ℕ) :
    ∀ m : ℕ, Finset.sum (Finset.range m) (fun k => f (2 * k) + f (2 * k + 1)) =
      Finset.sum (Finset.range (2 * m)) f
  | 0 => by simp
  | m + 1 => by
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [Finset.sum_range_succ, sum_range_pair f m, h2, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma treeLevelBits_sum_inv (N_bits : ℕ) (leaf : ℕ → Bool) (r : ℕ) :
    ∀ lvl : ℕ, lvl ≤ r →
      Finset.sum (Finset.range (2 ^ (r - lvl)))
        (fun node => bitsVal (lvl + 1) (treeLevelBits N_bits leaf lvl node)) =
      Finset.sum (Finset.range (2 ^ r))
        (fun i => if i < N_bits ∧ leaf i = true then 1 else 0)
  | 0, _ => by
    simp only [Nat.sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp only [bitsVal, pow_zero, Nat.mul_one, Nat.zero_add, treeLevelBits]
    by_cases hi : i < N_bits
    · cases leaf i <;> simp [hi]
    · simp [hi]
  | j + 1, hj => by
    have ih := treeLevelBits_sum_inv N_bits leaf r j (by omega)
    have hexp : 2 ^ (r - j) = 2 * 2 ^ (r - (j + 1)) := by
      have : r - j = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']
    rw [← ih, hexp, ← sum_range_pair]
    apply Finset.sum_congr rfl
    intro node _
    simp only [treeLevelBits, rippleSum_val]

lemma treeTop_val_eq_sum (N_bits : ℕ) (leaf : ℕ → Bool) :
    bitsVal (treeLog N_bits + 1) (treeLevelBits N_bits leaf (treeLog N_bits) 0) =
      Finset.sum (Finset.range N_bits) (fun i => if leaf i then 1 else 0) := by
  set r := treeLog N_bits
  have hinv := treeLevelBits_sum_inv N_bits leaf r r (Nat.le_refl r)
  simp only [Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton] at hinv
  rw [hinv]
  have hle : N_bits ≤ 2 ^ r := le_treeM N_bits
  have hsplit : 2 ^ r = N_bits + (2 ^ r - N_bits) := (Nat.add_sub_of_le hle).symm
  rw [hsplit, Finset.sum_range_add]
  have hright : Finset.sum (Finset.range (2 ^ r - N_bits))
      (fun k => if N_bits + k < N_bits ∧ leaf (N_bits + k) = true then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have : ¬(N_bits + k < N_bits) := by omega
    simp [this]
  rw [hright, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < N_bits := Finset.mem_range.mp hi
  cases leaf i <;> simp [hi']

/-- Ripple-borrow comparator pure function for `Le` (`sum ≤ t`). -/
def leBorrow (f : ℕ → Bool) (t : ℕ) : ℕ → Bool
  | 0 => false
  | b + 1 =>
    if t.testBit b then (f b && leBorrow f t b) else (f b || leBorrow f t b)

lemma leBorrow_invariant (f : ℕ → Bool) (t : ℕ) :
    ∀ b : ℕ, leBorrow f t b = decide (t % 2 ^ b < bitsVal b f)
  | 0 => by simp [leBorrow, bitsVal]
  | b + 1 => by
    simp only [leBorrow, leBorrow_invariant f t b, bitsVal]
    set v := bitsVal b f
    have hlt_f : v < 2 ^ b := bitsVal_lt_pow b f
    have hlt_t : t % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.one_le_pow b 2 (by decide))
    have hmod : t % 2 ^ (b + 1) = t % 2 ^ b + 2 ^ b * ((t / 2 ^ b) % 2) :=
      Nat.mod_pow_succ
    rw [hmod, Nat.testBit_eq_decide_div_mod_eq]
    have h2 : (t / 2 ^ b) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hlt_fb : bitsVal b f < 2 ^ b := hlt_f
    rcases Nat.eq_zero_or_pos ((t / 2 ^ b) % 2) with h0 | hpos
    · rcases Bool.eq_false_or_eq_true (f b) with hfb | hfb
      · simp [h0, hfb]; omega
      · simp [h0, hfb]
    · have h1 : (t / 2 ^ b) % 2 = 1 := by omega
      rcases Bool.eq_false_or_eq_true (f b) with hfb | hfb
      · simp [h1, hfb]
      · simp [h1, hfb]; omega

lemma bitsVal_le_iff_leBorrow (W : ℕ) (f : ℕ → Bool) (t : ℕ) :
    bitsVal W f ≤ t ↔ (if t < 2 ^ W then leBorrow f t W = false else True) := by
  have hlt_f : bitsVal W f < 2 ^ W := bitsVal_lt_pow W f
  split_ifs with ht
  · rw [leBorrow_invariant, decide_eq_false_iff_not, Nat.mod_eq_of_lt ht]
    omega
  · simp [show bitsVal W f ≤ t by omega]

/-- Closed-form edge and vertex offset functions for the balanced carry-ripple adder tree (§4.2). -/
def treeEdgeOff (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 1 => treeEdgeOff r j + (2 * j + 1) * 2 ^ (r - j)

def treeVertOff (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 1 => treeVertOff r j + (j + 1) * 2 ^ (r - j)

lemma treeEdgeOff_succ_r (r : ℕ) :
    ∀ k : ℕ, k ≤ r + 1 → treeEdgeOff (r + 1) k = 2 * treeEdgeOff r k
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hj => by
    have ih := treeEdgeOff_succ_r r (j + 1) (by omega)
    have hstep1 : treeEdgeOff (r + 1) (j + 2) =
        treeEdgeOff (r + 1) (j + 1) + (2 * (j + 1) + 1) * 2 ^ (r + 1 - (j + 1)) := rfl
    have hstep2 : treeEdgeOff r (j + 2) =
        treeEdgeOff r (j + 1) + (2 * (j + 1) + 1) * 2 ^ (r - (j + 1)) := rfl
    have hexp : 2 ^ (r + 1 - (j + 1)) = 2 * 2 ^ (r - (j + 1)) := by
      have : r + 1 - (j + 1) = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']
    rw [hstep1, hstep2, ih, hexp]
    ring

lemma treeEdgeOff_closed_form :
    ∀ r : ℕ, 1 ≤ r → treeEdgeOff r (r + 1) + 2 * r + 5 = 5 * 2 ^ r
  | 0, hr => by omega
  | 1, _ => rfl
  | r + 2, _ => by
    have ih : treeEdgeOff (r + 1) (r + 2) + 2 * (r + 1) + 5 = 5 * 2 ^ (r + 1) :=
      treeEdgeOff_closed_form (r + 1) (by omega)
    have hstep : treeEdgeOff (r + 2) (r + 3) =
        treeEdgeOff (r + 2) (r + 2) + (2 * (r + 2) + 1) * 2 ^ (r + 2 - (r + 2)) := rfl
    have h2 : treeEdgeOff (r + 2) (r + 2) = 2 * treeEdgeOff (r + 1) (r + 2) :=
      treeEdgeOff_succ_r (r + 1) (r + 2) (Nat.le_refl _)
    have hexp0 : 2 ^ (r + 2 - (r + 2)) = 1 := by simp
    have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [pow_succ']
    rw [hstep, h2, hexp0, hpow]
    omega

lemma treeEdgeOff_total_le {r : ℕ} (hr : 1 ≤ r) : treeEdgeOff r (r + 1) ≤ 5 * 2 ^ r := by
  have := treeEdgeOff_closed_form r hr
  omega

lemma treeVertOff_succ_r (r : ℕ) :
    ∀ k : ℕ, k ≤ r + 1 → treeVertOff (r + 1) k = 2 * treeVertOff r k
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hj => by
    have ih := treeVertOff_succ_r r (j + 1) (by omega)
    have hstep1 : treeVertOff (r + 1) (j + 2) =
        treeVertOff (r + 1) (j + 1) + (j + 2) * 2 ^ (r + 1 - (j + 1)) := rfl
    have hstep2 : treeVertOff r (j + 2) =
        treeVertOff r (j + 1) + (j + 2) * 2 ^ (r - (j + 1)) := rfl
    have hexp : 2 ^ (r + 1 - (j + 1)) = 2 * 2 ^ (r - (j + 1)) := by
      have : r + 1 - (j + 1) = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']
    rw [hstep1, hstep2, ih, hexp]
    ring

lemma treeVertOff_closed_form :
    ∀ r : ℕ, 1 ≤ r → treeVertOff r (r + 1) + r + 3 = 3 * 2 ^ r
  | 0, hr => by omega
  | 1, _ => rfl
  | r + 2, _ => by
    have ih : treeVertOff (r + 1) (r + 2) + (r + 1) + 3 = 3 * 2 ^ (r + 1) :=
      treeVertOff_closed_form (r + 1) (by omega)
    have hstep : treeVertOff (r + 2) (r + 3) =
        treeVertOff (r + 2) (r + 2) + (r + 3) * 2 ^ (r + 2 - (r + 2)) := rfl
    have h2 : treeVertOff (r + 2) (r + 2) = 2 * treeVertOff (r + 1) (r + 2) :=
      treeVertOff_succ_r (r + 1) (r + 2) (Nat.le_refl _)
    have hexp0 : 2 ^ (r + 2 - (r + 2)) = 1 := by simp
    have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [pow_succ']
    rw [hstep, h2, hexp0, hpow]
    omega

lemma treeVertOff_total_le {r : ℕ} (hr : 1 ≤ r) : treeVertOff r (r + 1) ≤ 3 * 2 ^ r := by
  have := treeVertOff_closed_form r hr
  omega

/-!
## Part 4: Unified `QCSD_BoolTensorNetwork2` Assembly (`Exact`, `Sep`, `Le`) & Prefix Pinning
-/

/-- 5-input `Sep` top-level full-adder circuit: checks full-adder equations AND pins `inp 0, inp 1`. -/
def sepFullAdderCircuit (guard : Bool) (t0Bit t1Bit : Bool) : QCSD_BoolCircuit :=
  if !guard then constCircuit 5 false
  else
    let gsBase := fullAdderCircuit.gates
    let c0 := emitConst gsBase t0Bit
    let eq0 := emitEq c0.1 0 c0.2
    let c1 := emitConst eq0.1 t1Bit
    let eq1 := emitEq c1.1 1 c1.2
    let a1 := emitConj eq1.1 (gsBase.length - 1) eq0.2
    let a2 := emitConj a1.1 a1.2 eq1.2
    ⟨5, a2.1⟩

lemma sepFullAdderCircuit_numInputs (guard t0Bit t1Bit : Bool) :
    (sepFullAdderCircuit guard t0Bit t1Bit).numInputs = 5 := by
  unfold sepFullAdderCircuit; split_ifs <;> rfl

lemma sepFullAdderCircuit_spec (guard t0Bit t1Bit : Bool) (inp : ℕ → Bool) :
    QCSD_circuitWF (sepFullAdderCircuit guard t0Bit t1Bit) ∧
    QCSD_evalCircuit (sepFullAdderCircuit guard t0Bit t1Bit) inp =
      (((inp 3 == bne (bne (inp 0) (inp 1)) (inp 2)) &&
        (inp 4 == ((inp 0 && inp 1) || ((inp 0 && inp 2) || (inp 1 && inp 2))))) &&
       (guard && (inp 0 == t0Bit) && (inp 1 == t1Bit))) ∧
    QCSD_circuitSize (sepFullAdderCircuit guard t0Bit t1Bit) ≤ 65 := by
  cases guard with
  | false =>
    dsimp [sepFullAdderCircuit]
    refine ⟨constCircuit_wf 5 false, ?_, by simp [constCircuit_size]⟩
    rw [constCircuit_eval]; simp
  | true =>
    have hwf : gatesWF 5 0 (sepFullAdderCircuit true t0Bit t1Bit).gates := by
      apply gatesWF_of_gatesWFB
      cases t0Bit <;> cases t1Bit <;> rfl
    refine ⟨circuitWF_of_gatesWF 5 _ hwf, ?_, by cases t0Bit <;> cases t1Bit <;> decide⟩
    have hcongr : QCSD_evalCircuit (sepFullAdderCircuit true t0Bit t1Bit) inp =
        QCSD_evalCircuit (sepFullAdderCircuit true t0Bit t1Bit)
          (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else if i = 2 then inp 2
            else if i = 3 then inp 3 else inp 4) := by
      apply evalCircuit_congr_lt _ hwf
      intro i hi
      change i < 5 at hi
      rcases i with _ | _ | _ | _ | _ | i' <;> try rfl
      omega
    rw [hcongr]
    generalize inp 0 = b0, inp 1 = b1, inp 2 = b2, inp 3 = b3, inp 4 = b4
    cases t0Bit <;> cases t1Bit <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

/-- 3-input `Exact` comparator-slot circuit: checks `guard && (inp 0 == tBit) && (inp 2 == false)`. -/
def exactCmpStepCircuit (guard tBit : Bool) : QCSD_BoolCircuit :=
  if !guard then constCircuit 3 false
  else
    let gs0 : List QCSD_Gate :=
      [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩]
    let cT := emitConst gs0 tBit
    let eq0 := emitEq cT.1 0 cT.2
    let n2 := emitNeg eq0.1 2
    let all := emitConj n2.1 eq0.2 n2.2
    ⟨3, all.1⟩

lemma exactCmpStepCircuit_numInputs (guard tBit : Bool) :
    (exactCmpStepCircuit guard tBit).numInputs = 3 := by
  unfold exactCmpStepCircuit; split_ifs <;> rfl

lemma exactCmpStepCircuit_spec (guard tBit : Bool) (inp : ℕ → Bool) :
    QCSD_circuitWF (exactCmpStepCircuit guard tBit) ∧
    QCSD_evalCircuit (exactCmpStepCircuit guard tBit) inp =
      (guard && (inp 0 == tBit) && (inp 2 == false)) ∧
    QCSD_circuitSize (exactCmpStepCircuit guard tBit) ≤ 20 := by
  cases guard with
  | false =>
    dsimp [exactCmpStepCircuit]
    refine ⟨constCircuit_wf 3 false, ?_, by simp [constCircuit_size]⟩
    rw [constCircuit_eval]; simp
  | true =>
    have hwf : gatesWF 3 0 (exactCmpStepCircuit true tBit).gates := by
      apply gatesWF_of_gatesWFB
      cases tBit <;> rfl
    refine ⟨circuitWF_of_gatesWF 3 _ hwf, ?_, by cases tBit <;> decide⟩
    have hcongr : QCSD_evalCircuit (exactCmpStepCircuit true tBit) inp =
        QCSD_evalCircuit (exactCmpStepCircuit true tBit)
          (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else inp 2) := by
      apply evalCircuit_congr_lt _ hwf
      intro i hi
      change i < 3 at hi
      rcases i with _ | _ | _ | i' <;> try rfl
      omega
    rw [hcongr]
    generalize inp 0 = b0, inp 1 = b1, inp 2 = b2
    cases tBit <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-- 3-input `Sep` comparator-slot circuit: forces `inp 2 == false`. -/
def sepCmpStepCircuit : QCSD_BoolCircuit :=
  ⟨3, [⟨QCSD_GateOp.input, 2, 0⟩, ⟨QCSD_GateOp.neg, 0, 0⟩]⟩

lemma sepCmpStepCircuit_numInputs : sepCmpStepCircuit.numInputs = 3 := rfl

lemma sepCmpStepCircuit_spec (inp : ℕ → Bool) :
    QCSD_circuitWF sepCmpStepCircuit ∧
    QCSD_evalCircuit sepCmpStepCircuit inp = (inp 2 == false) ∧
    QCSD_circuitSize sepCmpStepCircuit ≤ 10 := by
  have hwf : gatesWF 3 0 sepCmpStepCircuit.gates := gatesWF_of_gatesWFB 3 _ 0 rfl
  refine ⟨circuitWF_of_gatesWF 3 _ hwf, ?_, by decide⟩
  have hcongr : QCSD_evalCircuit sepCmpStepCircuit inp =
      QCSD_evalCircuit sepCmpStepCircuit
        (fun i => if i = 0 then inp 0 else if i = 1 then inp 1 else inp 2) := by
    apply evalCircuit_congr_lt _ hwf
    intro i hi
    change i < 3 at hi
    rcases i with _ | _ | _ | i' <;> try rfl
    omega
  rw [hcongr]
  generalize inp 0 = b0, inp 1 = b1, inp 2 = b2
  cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-! ### Bound on `fwdSt1InIndices` Length -/

lemma fwdSt1InIndices_length_le {n : ℕ} (hn : 1 ≤ n) (j2 : ℕ) :
    (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length ≤ paramJ n * paramL1 n := by
  set J := paramJ n
  set L1 := paramL1 n
  set L2 := paramL2 n
  have hJ : 0 < J := paramJ_pos n
  have hL2 : 0 < L2 := one_le_paramL2 n
  unfold fwdSt1InIndices
  have hnodup : ((List.range n).filter (fun idx => decide ((idx / J) % L2 = j2))).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnodup]
  set s := ((List.range n).filter (fun idx => decide ((idx / J) % L2 = j2))).toFinset
  have hcard : s.card ≤ (Finset.range (L1 * J)).card := by
    apply Finset.card_le_card_of_injOn (fun idx => ((idx / J) / L2) * J + idx % J)
    · intro idx hidx
      have hidx' : idx ∈ s := Finset.mem_coe.mp hidx
      dsimp only [s] at hidx'
      rw [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hidx'
      rw [Finset.mem_coe, Finset.mem_range]
      have h_lt_LJ : idx < (L1 * L2) * J := by
        calc
          idx < n := hidx'.1
          _ ≤ paramM n * J := le_paramM_mul_paramJ n
          _ ≤ paramL n * J := Nat.mul_le_mul_right J (paramM_le_paramL hn)
          _ = (L1 * L2) * J := by rw [paramL_eq_mul]
      have hdiv1 : idx / J < L1 * L2 :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using h_lt_LJ)
      have hdiv2 : (idx / J) / L2 < L1 :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hdiv1)
      have hmod : idx % J < J := Nat.mod_lt idx hJ
      have : ((idx / J) / L2) * J + idx % J < ((idx / J) / L2 + 1) * J := by
        have : ((idx / J) / L2 + 1) * J = ((idx / J) / L2) * J + J := by ring
        omega
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right J hdiv2)
    · intro a ha b hb heq
      have ha' : a ∈ s := Finset.mem_coe.mp ha
      have hb' : b ∈ s := Finset.mem_coe.mp hb
      dsimp only [s] at ha' hb'
      rw [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at ha' hb'
      have hma : a % J < J := Nat.mod_lt a hJ
      have hmb : b % J < J := Nat.mod_lt b hJ
      have hmod_eq : a % J = b % J := by
        have h1 : (((a / J) / L2) * J + a % J) % J = (((b / J) / L2) * J + b % J) % J :=
          congrArg (· % J) heq
        simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hma, Nat.mod_eq_of_lt hmb] using h1
      have hq_eq : (a / J) / L2 = (b / J) / L2 := by
        dsimp only at heq
        rw [hmod_eq] at heq
        have hmul_eq : ((a / J) / L2) * J = ((b / J) / L2) * J := Nat.add_right_cancel heq
        exact Nat.eq_of_mul_eq_mul_right hJ hmul_eq
      have hblk_eq : a / J = b / J := by
        have da := Nat.div_add_mod (a / J) L2
        have db := Nat.div_add_mod (b / J) L2
        rw [ha'.2, hq_eq] at da
        rw [hb'.2] at db
        omega
      have da2 := Nat.div_add_mod a J
      have db2 := Nat.div_add_mod b J
      rw [hblk_eq, hmod_eq] at da2
      omega
  rw [Finset.card_range, Nat.mul_comm] at hcard
  exact hcard

/-! ### Adder Tree Level/Node/Offset Codecs (`decodeTreeEdge` and `decodeTreeVert`) -/

lemma treeEdgeOff_mono (r : ℕ) : ∀ {a b : ℕ}, a ≤ b → treeEdgeOff r a ≤ treeEdgeOff r b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    cases m with
    | zero => exact ih
    | succ m' =>
      change treeEdgeOff r a ≤ treeEdgeOff r (m' + 2)
      have h : treeEdgeOff r (m' + 2) = treeEdgeOff r (m' + 1) + (2 * (m' + 1) + 1) * 2 ^ (r - (m' + 1)) := rfl
      omega

lemma treeVertOff_mono (r : ℕ) : ∀ {a b : ℕ}, a ≤ b → treeVertOff r a ≤ treeVertOff r b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    cases m with
    | zero => exact ih
    | succ m' =>
      change treeVertOff r a ≤ treeVertOff r (m' + 2)
      have h : treeVertOff r (m' + 2) = treeVertOff r (m' + 1) + (m' + 2) * 2 ^ (r - (m' + 1)) := rfl
      omega

def decodeTreeEdgeAux (r rem : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, j => (j, 0, 0)
  | fuel + 1, j =>
    let blk := (2 * j + 1) * 2 ^ (r - j)
    if rem < blk then (j, rem / (2 * j + 1), rem % (2 * j + 1))
    else decodeTreeEdgeAux r (rem - blk) fuel (j + 1)

def decodeTreeEdge (r locE : ℕ) : ℕ × ℕ × ℕ :=
  decodeTreeEdgeAux r locE r 1

lemma decodeTreeEdgeAux_spec (r : ℕ) :
    ∀ (fuel j rem : ℕ),
      1 ≤ j →
      j + fuel = r + 1 →
      treeEdgeOff r j + rem < treeEdgeOff r (r + 1) →
      let t := decodeTreeEdgeAux r rem fuel j
      1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < 2 * t.1 + 1 ∧
      treeEdgeOff r j + rem = treeEdgeOff r t.1 + t.2.1 * (2 * t.1 + 1) + t.2.2
  | 0, j, rem, _, hjf, hlt => by
    have : j = r + 1 := by omega
    subst this; omega
  | fuel + 1, j, rem, hj1, hjf, hlt => by
    simp only [decodeTreeEdgeAux]
    set blk := (2 * j + 1) * 2 ^ (r - j)
    split_ifs with hrem
    · dsimp only
      have hdiv : rem / (2 * j + 1) < 2 ^ (r - j) :=
        Nat.div_lt_of_lt_mul hrem
      have hmod : rem % (2 * j + 1) < 2 * j + 1 := Nat.mod_lt _ (by omega)
      have hdm := Nat.div_add_mod rem (2 * j + 1)
      have hcomm : (2 * j + 1) * (rem / (2 * j + 1)) = (rem / (2 * j + 1)) * (2 * j + 1) :=
        Nat.mul_comm _ _
      exact ⟨hj1, by omega, hdiv, hmod, by omega⟩
    · have hstep : treeEdgeOff r (j + 1) = treeEdgeOff r j + blk := by
        cases j with
        | zero => omega
        | succ j' => rfl
      have hrec := decodeTreeEdgeAux_spec r fuel (j + 1) (rem - blk)
        (by omega) (by omega) (by omega)
      exact ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, by have := hrec.2.2.2.2; omega⟩

lemma decodeTreeEdge_spec {r locE : ℕ} (hloc : locE < treeEdgeOff r (r + 1)) :
    let t := decodeTreeEdge r locE
    1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < 2 * t.1 + 1 ∧
    locE = treeEdgeOff r t.1 + t.2.1 * (2 * t.1 + 1) + t.2.2 := by
  have h := decodeTreeEdgeAux_spec r r 1 locE (by omega) (by omega)
    (by simpa [treeEdgeOff] using hloc)
  simpa [decodeTreeEdge, treeEdgeOff] using h

lemma encodeTreeEdge_lt {r j node w : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hw : w < 2 * j + 1) :
    treeEdgeOff r j + node * (2 * j + 1) + w < treeEdgeOff r (r + 1) := by
  have h1 : node * (2 * j + 1) + w < (node + 1) * (2 * j + 1) := by
    have : (node + 1) * (2 * j + 1) = node * (2 * j + 1) + (2 * j + 1) := by ring
    omega
  have h2 : (node + 1) * (2 * j + 1) ≤ 2 ^ (r - j) * (2 * j + 1) :=
    Nat.mul_le_mul_right _ hnode
  have h3 : treeEdgeOff r (j + 1) = treeEdgeOff r j + (2 * j + 1) * 2 ^ (r - j) := by
    cases j with
    | zero => omega
    | succ j' => rfl
  have h4 : treeEdgeOff r (j + 1) ≤ treeEdgeOff r (r + 1) :=
    treeEdgeOff_mono r (by omega)
  have hcomm : 2 ^ (r - j) * (2 * j + 1) = (2 * j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  omega

lemma encodeTreeEdge_inj {r j1 n1 w1 j2 n2 w2 : ℕ}
    (hj1_lo : 1 ≤ j1) (hn1 : n1 < 2 ^ (r - j1)) (hw1 : w1 < 2 * j1 + 1)
    (hj2_lo : 1 ≤ j2) (hn2 : n2 < 2 ^ (r - j2)) (hw2 : w2 < 2 * j2 + 1)
    (heq : treeEdgeOff r j1 + n1 * (2 * j1 + 1) + w1 =
           treeEdgeOff r j2 + n2 * (2 * j2 + 1) + w2) :
    j1 = j2 ∧ n1 = n2 ∧ w1 = w2 := by
  have hj_eq : j1 = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | rfl | hgt
    · have hb1 : treeEdgeOff r j1 + n1 * (2 * j1 + 1) + w1 < treeEdgeOff r (j1 + 1) := by
        have hstep : treeEdgeOff r (j1 + 1) = treeEdgeOff r j1 + (2 * j1 + 1) * 2 ^ (r - j1) := by
          cases j1 with | zero => omega | succ _ => rfl
        have hmul : (n1 + 1) * (2 * j1 + 1) ≤ 2 ^ (r - j1) * (2 * j1 + 1) :=
          Nat.mul_le_mul_right _ hn1
        have hcomm : 2 ^ (r - j1) * (2 * j1 + 1) = (2 * j1 + 1) * 2 ^ (r - j1) := Nat.mul_comm _ _
        have hlin : (n1 + 1) * (2 * j1 + 1) = n1 * (2 * j1 + 1) + (2 * j1 + 1) := by ring
        omega
      have hb2 : treeEdgeOff r (j1 + 1) ≤ treeEdgeOff r j2 := treeEdgeOff_mono r hlt
      omega
    · rfl
    · have hb2 : treeEdgeOff r j2 + n2 * (2 * j2 + 1) + w2 < treeEdgeOff r (j2 + 1) := by
        have hstep : treeEdgeOff r (j2 + 1) = treeEdgeOff r j2 + (2 * j2 + 1) * 2 ^ (r - j2) := by
          cases j2 with | zero => omega | succ _ => rfl
        have hmul : (n2 + 1) * (2 * j2 + 1) ≤ 2 ^ (r - j2) * (2 * j2 + 1) :=
          Nat.mul_le_mul_right _ hn2
        have hcomm : 2 ^ (r - j2) * (2 * j2 + 1) = (2 * j2 + 1) * 2 ^ (r - j2) := Nat.mul_comm _ _
        have hlin : (n2 + 1) * (2 * j2 + 1) = n2 * (2 * j2 + 1) + (2 * j2 + 1) := by ring
        omega
      have hb1 : treeEdgeOff r (j2 + 1) ≤ treeEdgeOff r j1 := treeEdgeOff_mono r hgt
      omega
  subst hj_eq
  have hsub : n1 * (2 * j1 + 1) + w1 = n2 * (2 * j1 + 1) + w2 := by omega
  have hw_eq : w1 = w2 := by
    have hm := congrArg (· % (2 * j1 + 1)) hsub
    simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hw1, Nat.mod_eq_of_lt hw2] using hm
  subst hw_eq
  have hn_mul : n1 * (2 * j1 + 1) = n2 * (2 * j1 + 1) := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hn_mul, rfl⟩

lemma decodeTreeEdge_encode {r j node w : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hw : w < 2 * j + 1) :
    decodeTreeEdge r (treeEdgeOff r j + node * (2 * j + 1) + w) = (j, node, w) := by
  have hlt := encodeTreeEdge_lt hj1 hjr hnode hw
  have hsp := decodeTreeEdge_spec hlt
  set t := decodeTreeEdge r (treeEdgeOff r j + node * (2 * j + 1) + w)
  obtain ⟨e1, e2, e3⟩ := encodeTreeEdge_inj hsp.1 hsp.2.2.1 hsp.2.2.2.1 hj1 hnode hw hsp.2.2.2.2.symm
  rcases t with ⟨tj, tn, tw⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

def decodeTreeVertAux (r rem : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, j => (j, 0, 0)
  | fuel + 1, j =>
    let blk := (j + 1) * 2 ^ (r - j)
    if rem < blk then (j, rem / (j + 1), rem % (j + 1))
    else decodeTreeVertAux r (rem - blk) fuel (j + 1)

def decodeTreeVert (r locV : ℕ) : ℕ × ℕ × ℕ :=
  decodeTreeVertAux r locV r 1

lemma decodeTreeVertAux_spec (r : ℕ) :
    ∀ (fuel j rem : ℕ),
      1 ≤ j →
      j + fuel = r + 1 →
      treeVertOff r j + rem < treeVertOff r (r + 1) →
      let t := decodeTreeVertAux r rem fuel j
      1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < t.1 + 1 ∧
      treeVertOff r j + rem = treeVertOff r t.1 + t.2.1 * (t.1 + 1) + t.2.2
  | 0, j, rem, _, hjf, hlt => by
    have : j = r + 1 := by omega
    subst this; omega
  | fuel + 1, j, rem, hj1, hjf, hlt => by
    simp only [decodeTreeVertAux]
    set blk := (j + 1) * 2 ^ (r - j)
    split_ifs with hrem
    · dsimp only
      have hdiv : rem / (j + 1) < 2 ^ (r - j) := Nat.div_lt_of_lt_mul hrem
      have hmod : rem % (j + 1) < j + 1 := Nat.mod_lt _ (by omega)
      have hdm := Nat.div_add_mod rem (j + 1)
      have hcomm : (j + 1) * (rem / (j + 1)) = (rem / (j + 1)) * (j + 1) := Nat.mul_comm _ _
      exact ⟨hj1, by omega, hdiv, hmod, by omega⟩
    · have hstep : treeVertOff r (j + 1) = treeVertOff r j + blk := by
        cases j with | zero => omega | succ _ => rfl
      have hrec := decodeTreeVertAux_spec r fuel (j + 1) (rem - blk)
        (by omega) (by omega) (by omega)
      exact ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, by have := hrec.2.2.2.2; omega⟩

lemma decodeTreeVert_spec {r locV : ℕ} (hloc : locV < treeVertOff r (r + 1)) :
    let t := decodeTreeVert r locV
    1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < t.1 + 1 ∧
    locV = treeVertOff r t.1 + t.2.1 * (t.1 + 1) + t.2.2 := by
  have h := decodeTreeVertAux_spec r r 1 locV (by omega) (by omega)
    (by simpa [treeVertOff] using hloc)
  simpa [decodeTreeVert, treeVertOff] using h

lemma encodeTreeVert_lt {r j node u : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hu : u < j + 1) :
    treeVertOff r j + node * (j + 1) + u < treeVertOff r (r + 1) := by
  have h1 : node * (j + 1) + u < (node + 1) * (j + 1) := by
    have : (node + 1) * (j + 1) = node * (j + 1) + (j + 1) := by ring
    omega
  have h2 : (node + 1) * (j + 1) ≤ 2 ^ (r - j) * (j + 1) :=
    Nat.mul_le_mul_right _ hnode
  have h3 : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := by
    cases j with | zero => omega | succ _ => rfl
  have h4 : treeVertOff r (j + 1) ≤ treeVertOff r (r + 1) :=
    treeVertOff_mono r (by omega)
  have hcomm : 2 ^ (r - j) * (j + 1) = (j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  omega

lemma encodeTreeVert_inj {r j1 n1 u1 j2 n2 u2 : ℕ}
    (hj1_lo : 1 ≤ j1) (hn1 : n1 < 2 ^ (r - j1)) (hu1 : u1 < j1 + 1)
    (hj2_lo : 1 ≤ j2) (hn2 : n2 < 2 ^ (r - j2)) (hu2 : u2 < j2 + 1)
    (heq : treeVertOff r j1 + n1 * (j1 + 1) + u1 =
           treeVertOff r j2 + n2 * (j2 + 1) + u2) :
    j1 = j2 ∧ n1 = n2 ∧ u1 = u2 := by
  have hj_eq : j1 = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | rfl | hgt
    · have hb1 : treeVertOff r j1 + n1 * (j1 + 1) + u1 < treeVertOff r (j1 + 1) := by
        have hstep : treeVertOff r (j1 + 1) = treeVertOff r j1 + (j1 + 1) * 2 ^ (r - j1) := by
          cases j1 with | zero => omega | succ _ => rfl
        have hmul : (n1 + 1) * (j1 + 1) ≤ 2 ^ (r - j1) * (j1 + 1) :=
          Nat.mul_le_mul_right _ hn1
        have hcomm : 2 ^ (r - j1) * (j1 + 1) = (j1 + 1) * 2 ^ (r - j1) := Nat.mul_comm _ _
        have hlin : (n1 + 1) * (j1 + 1) = n1 * (j1 + 1) + (j1 + 1) := by ring
        omega
      have hb2 : treeVertOff r (j1 + 1) ≤ treeVertOff r j2 := treeVertOff_mono r hlt
      omega
    · rfl
    · have hb2 : treeVertOff r j2 + n2 * (j2 + 1) + u2 < treeVertOff r (j2 + 1) := by
        have hstep : treeVertOff r (j2 + 1) = treeVertOff r j2 + (j2 + 1) * 2 ^ (r - j2) := by
          cases j2 with | zero => omega | succ _ => rfl
        have hmul : (n2 + 1) * (j2 + 1) ≤ 2 ^ (r - j2) * (j2 + 1) :=
          Nat.mul_le_mul_right _ hn2
        have hcomm : 2 ^ (r - j2) * (j2 + 1) = (j2 + 1) * 2 ^ (r - j2) := Nat.mul_comm _ _
        have hlin : (n2 + 1) * (j2 + 1) = n2 * (j2 + 1) + (j2 + 1) := by ring
        omega
      have hb1 : treeVertOff r (j2 + 1) ≤ treeVertOff r j1 := treeVertOff_mono r hgt
      omega
  subst hj_eq
  have hsub : n1 * (j1 + 1) + u1 = n2 * (j1 + 1) + u2 := by omega
  have hu_eq : u1 = u2 := by
    have hm := congrArg (· % (j1 + 1)) hsub
    simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hu2] using hm
  subst hu_eq
  have hn_mul : n1 * (j1 + 1) = n2 * (j1 + 1) := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hn_mul, rfl⟩

lemma decodeTreeVert_encode {r j node u : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hu : u < j + 1) :
    decodeTreeVert r (treeVertOff r j + node * (j + 1) + u) = (j, node, u) := by
  have hlt := encodeTreeVert_lt hj1 hjr hnode hu
  have hsp := decodeTreeVert_spec hlt
  set t := decodeTreeVert r (treeVertOff r j + node * (j + 1) + u)
  obtain ⟨e1, e2, e3⟩ := encodeTreeVert_inj hsp.1 hsp.2.2.1 hsp.2.2.2.1 hj1 hnode hu hsp.2.2.2.2.symm
  rcases t with ⟨tj, tn, tu⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

/-! ### Unified Network Vertex & Edge Offsets and `rawEnds` -/

def netV0 (_n : ℕ) : ℕ := 0
def netV1 (n : ℕ) : ℕ := 2 * n
def netV2 (n : ℕ) : ℕ := 4 * n
def netV3 (n : ℕ) : ℕ := 5 * n
def netV4 (n : ℕ) : ℕ := 5 * n + paramL2 n
def netV5 (n : ℕ) : ℕ := 5 * n + paramL2 n + paramL1 n
def netV6 (n : ℕ) : ℕ := 5 * n + 2 * paramL2 n + paramL1 n
def netV7 (n : ℕ) : ℕ := 5 * n + 2 * paramL2 n + 2 * paramL1 n
def netV8 (n : ℕ) : ℕ := netV7 n + paramL n
def netV9 (n : ℕ) : ℕ := netV8 n + paramL2 n
def netV10 (n : ℕ) : ℕ := netV9 n + paramL1 n
def netV11 (n : ℕ) : ℕ := netV10 n + 2 * paramJ n * paramL n
def netV12 (n : ℕ) : ℕ := netV11 n + 2 * n
def netV13 (n : ℕ) : ℕ := netV12 n + n
def netV14 (n : ℕ) : ℕ := netV13 n + (treeM n - n)
def netV15 (n : ℕ) : ℕ := netV14 n + (treeM n - n)
def netV16 (n : ℕ) : ℕ := netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2)
def netV17 (n : ℕ) : ℕ := netV16 n + 1
def netV18 (n : ℕ) : ℕ := netV17 n + (treeLog n + 2)
def netVertCount (n : ℕ) : ℕ := netV18 n + 1

def netE0 (_n : ℕ) : ℕ := 0
def netE1 (n : ℕ) : ℕ := 2 * n
def netE2 (n : ℕ) : ℕ := 4 * n
def netE3 (n : ℕ) : ℕ := 4 * n + 2 * treeM n
def netE4 (n : ℕ) : ℕ := netE3 n + n
def netE5 (n : ℕ) : ℕ := netE4 n + 2 * paramJ n * paramL n
def netE6 (n : ℕ) : ℕ := netE5 n + 2 * paramJ n * paramL n
def netE7 (n : ℕ) : ℕ := netE6 n + 2 * paramJ n * paramL n
def netE8 (n : ℕ) : ℕ := netE7 n + 2 * paramJ n * paramL n
def netE9 (n : ℕ) : ℕ := netE8 n + 2 * paramJ n * paramL n
def netE10 (n : ℕ) : ℕ := netE9 n + 2 * paramJ n * paramL n
def netE11 (n : ℕ) : ℕ := netE10 n + 2 * paramJ n * paramL n
def netE12 (n : ℕ) : ℕ := netE11 n + 2 * n
def netE13 (n : ℕ) : ℕ := netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 2)
def netEdgeCount (n : ℕ) : ℕ := netE13 n + (treeLog n + 3)

def ovlTargetBit (J blk p : ℕ) : ℕ :=
  if p < J then blk * J + p else (blk + 1) * J + (p - J)

/-- Per-block endpoint helpers (`endsB0 .. endsB13`) so `rawEnds` peels one branch at a time. -/
def endsB0 (n e : ℕ) : ℕ × ℕ := (netV0 n + e, netV1 n + e)

def endsB1 (n i : ℕ) : ℕ × ℕ :=
  (netV1 n + i, if i < n then netV12 n + i else netV5 n + (((i - n) / paramJ n) % paramL2 n))

def endsB2 (n leaf : ℕ) : ℕ × ℕ :=
  let M1 := treeM n
  let src :=
    if leaf < n then netV1 n + leaf
    else if leaf < M1 then netV13 n + (leaf - n)
    else if leaf < M1 + n then netV1 n + n + (leaf - M1)
    else netV14 n + (leaf - (M1 + n))
  (src, netV15 n + (leaf / 2) * 2 + 1)

def endsB3 (n idx : ℕ) : ℕ × ℕ :=
  (netV2 n + idx, netV3 n + ((idx / paramJ n) % paramL2 n))

def endsB4 (n k : ℕ) : ℕ × ℕ :=
  let rem := k / (2 * paramJ n)
  (netV3 n + rem / paramL1 n, netV4 n + rem % paramL1 n)

def endsB5 (n k : ℕ) : ℕ × ℕ :=
  let q := k / (2 * paramJ n)
  (netV4 n + q % paramL1 n, netV7 n + q)

def endsB6 (n k : ℕ) : ℕ × ℕ :=
  let rem := k / (2 * paramJ n)
  (netV5 n + rem / paramL1 n, netV6 n + rem % paramL1 n)

def endsB7 (n k : ℕ) : ℕ × ℕ :=
  let q := k / (2 * paramJ n)
  (netV6 n + q % paramL1 n, netV7 n + q)

def endsB8 (n k : ℕ) : ℕ × ℕ :=
  let q := k / (2 * paramJ n)
  (netV7 n + q, netV8 n + q % paramL2 n)

def endsB9 (n k : ℕ) : ℕ × ℕ :=
  let rem := k / (2 * paramJ n)
  (netV8 n + rem / paramL1 n, netV9 n + rem % paramL1 n)

def endsB10 (n k : ℕ) : ℕ × ℕ :=
  let J := paramJ n
  let blk := k / (2 * J)
  let p := k % (2 * J)
  let tk := ovlTargetBit J blk p
  (netV9 n + blk % paramL1 n, if tk < 2 * n then netV11 n + tk else netV10 n + k)

def endsB11 (n k : ℕ) : ℕ × ℕ :=
  (netV11 n + k, netV12 n + k % n)

def endsB12 (n locE : ℕ) : ℕ × ℕ :=
  let r := treeLog n + 1
  let t := decodeTreeEdge r locE
  let j := t.1
  let node := t.2.1
  let w := t.2.2
  let src :=
    if w = 0 then netV15 n + treeVertOff r j + node * (j + 1)
    else netV15 n + treeVertOff r j + node * (j + 1) + 1 + (w - 1) / 2
  let dst :=
    if w % 2 = 0 ∧ w < 2 * j then
      netV15 n + treeVertOff r j + node * (j + 1) + 1 + w / 2
    else
      let bitIdx := if w = 2 * j then j else w / 2
      if j < r then
        netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) + 1 + bitIdx
      else
        netV17 n + bitIdx
  (src, dst)

def endsB13 (n b : ℕ) : ℕ × ℕ :=
  let W := treeLog n + 2
  (if b = 0 then netV16 n else netV17 n + (b - 1),
   if b < W then netV17 n + b else netV18 n)

def rawEnds (n e : ℕ) : ℕ × ℕ :=
  if e < netE1 n then endsB0 n e
  else if e < netE2 n then endsB1 n (e - netE1 n)
  else if e < netE3 n then endsB2 n (e - netE2 n)
  else if e < netE4 n then endsB3 n (e - netE3 n)
  else if e < netE5 n then endsB4 n (e - netE4 n)
  else if e < netE6 n then endsB5 n (e - netE5 n)
  else if e < netE7 n then endsB6 n (e - netE6 n)
  else if e < netE8 n then endsB7 n (e - netE7 n)
  else if e < netE9 n then endsB8 n (e - netE8 n)
  else if e < netE10 n then endsB9 n (e - netE9 n)
  else if e < netE11 n then endsB10 n (e - netE10 n)
  else if e < netE12 n then endsB11 n (e - netE11 n)
  else if e < netE13 n then endsB12 n (e - netE12 n)
  else endsB13 n (e - netE13 n)

lemma netV_chain (n : ℕ) :
    netV0 n ≤ netV1 n ∧ netV1 n ≤ netV2 n ∧ netV2 n ≤ netV3 n ∧ netV3 n ≤ netV4 n ∧
    netV4 n ≤ netV5 n ∧ netV5 n ≤ netV6 n ∧ netV6 n ≤ netV7 n ∧ netV7 n ≤ netV8 n ∧
    netV8 n ≤ netV9 n ∧ netV9 n ≤ netV10 n ∧ netV10 n ≤ netV11 n ∧ netV11 n ≤ netV12 n ∧
    netV12 n ≤ netV13 n ∧ netV13 n ≤ netV14 n ∧ netV14 n ≤ netV15 n ∧ netV15 n ≤ netV16 n ∧
    netV16 n ≤ netV17 n ∧ netV17 n < netV18 n ∧ netV18 n < netVertCount n := by
  simp only [netV0, netV1, netV2, netV3, netV4, netV5, netV6, netV7, netV8, netV9,
             netV10, netV11, netV12, netV13, netV14, netV15, netV16, netV17, netV18, netVertCount]
  omega

lemma rawEnds_lt_and_bound (n : ℕ) (e : ℕ) (he : e < netEdgeCount n) :
    (rawEnds n e).1 < (rawEnds n e).2 ∧ (rawEnds n e).2 < netVertCount n := by
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netV_chain n with
    ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18⟩
  unfold rawEnds
  by_cases he1 : e < netE1 n
  · simp only [he1, ↓reduceIte]
    dsimp [endsB0, netV0, netV1]; have : netV2 n = 4 * n := rfl; change e < 2 * n at he1; omega
  simp only [he1, ↓reduceIte]
  by_cases he2 : e < netE2 n
  · simp only [he2, ↓reduceIte]
    dsimp [endsB1]
    have : netE1 n = 2 * n := rfl; have : netE2 n = 4 * n := rfl
    have : netV1 n = 2 * n := rfl; have : netV2 n = 4 * n := rfl
    have : netV6 n = netV5 n + paramL2 n := by simp [netV5, netV6]; omega
    have : netV13 n = netV12 n + n := rfl
    have hmod : (((e - netE1 n) - n) / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
    split_ifs <;> omega
  simp only [he2, ↓reduceIte]
  by_cases he3 : e < netE3 n
  · simp only [he3, ↓reduceIte]
    dsimp [endsB2]
    have : netE2 n = 4 * n := rfl; have : netE3 n = 4 * n + 2 * treeM n := rfl
    set leaf := e - netE2 n
    have hleaf : leaf < 2 * treeM n := by omega
    have hsrc : (if leaf < n then netV1 n + leaf
        else if leaf < treeM n then netV13 n + (leaf - n)
        else if leaf < treeM n + n then netV1 n + n + (leaf - treeM n)
        else netV14 n + (leaf - (treeM n + n))) < netV15 n := by
      have : netV1 n = 2 * n := rfl; have : netV2 n = 4 * n := rfl
      have : netV14 n = netV13 n + (treeM n - n) := rfl
      have : netV15 n = netV14 n + (treeM n - n) := rfl
      split_ifs <;> omega
    have hdst : (leaf / 2) * 2 + 1 < treeVertOff (treeLog n + 1) (treeLog n + 2) := by
      have hnode : leaf / 2 < 2 ^ ((treeLog n + 1) - 1) := by
        simpa [treeM] using Nat.div_lt_of_lt_mul hleaf
      simpa [treeVertOff] using encodeTreeVert_lt (r := treeLog n + 1) (j := 1)
        (node := leaf / 2) (u := 1) (by omega) (by omega) hnode (by omega)
    have : netV16 n = netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) := rfl
    omega
  simp only [he3, ↓reduceIte]
  by_cases he4 : e < netE4 n
  · simp only [he4, ↓reduceIte]
    dsimp [endsB3]
    have : netE4 n = netE3 n + n := rfl
    have : netV3 n = netV2 n + n := by simp [netV2, netV3]; omega
    have : netV4 n = netV3 n + paramL2 n := by simp [netV3, netV4]
    have hmod : ((e - netE3 n) / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
    omega
  simp only [he4, ↓reduceIte]
  by_cases he5 : e < netE5 n
  · simp only [he5, ↓reduceIte]
    dsimp [endsB4]
    have : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
    have hk : e - netE4 n < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
      calc e - netE4 n < 2 * paramJ n * paramL n := by omega
           _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by rw [hL_mul]; ring
    have hrem : (e - netE4 n) / (2 * paramJ n) < paramL2 n * paramL1 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
    have hj2 : ((e - netE4 n) / (2 * paramJ n)) / paramL1 n < paramL2 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : ((e - netE4 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    have : netV4 n = netV3 n + paramL2 n := by simp [netV3, netV4]
    have : netV5 n = netV4 n + paramL1 n := by simp [netV4, netV5]
    omega
  simp only [he5, ↓reduceIte]
  by_cases he6 : e < netE6 n
  · simp only [he6, ↓reduceIte]
    dsimp [endsB5]
    have : netE6 n = netE5 n + 2 * paramJ n * paramL n := rfl
    have hq : (e - netE5 n) / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul (by omega)
    have hq1 : ((e - netE5 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    generalize (e - netE5 n) / (2 * paramJ n) = q at hq hq1 ⊢
    have : netV5 n = netV4 n + paramL1 n := by simp [netV4, netV5]
    have : netV5 n ≤ netV7 n := by simp [netV5, netV7]; omega
    have : netV8 n = netV7 n + paramL n := rfl
    omega
  simp only [he6, ↓reduceIte]
  by_cases he7 : e < netE7 n
  · simp only [he7, ↓reduceIte]
    dsimp [endsB6]
    have : netE7 n = netE6 n + 2 * paramJ n * paramL n := rfl
    have hk : e - netE6 n < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
      calc e - netE6 n < 2 * paramJ n * paramL n := by omega
           _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by rw [hL_mul]; ring
    have hrem : (e - netE6 n) / (2 * paramJ n) < paramL2 n * paramL1 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
    have hj2 : ((e - netE6 n) / (2 * paramJ n)) / paramL1 n < paramL2 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : ((e - netE6 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    have : netV6 n = netV5 n + paramL2 n := by simp [netV5, netV6]; omega
    have : netV7 n = netV6 n + paramL1 n := by simp [netV6, netV7]; omega
    omega
  simp only [he7, ↓reduceIte]
  by_cases he8 : e < netE8 n
  · simp only [he8, ↓reduceIte]
    dsimp [endsB7]
    have : netE8 n = netE7 n + 2 * paramJ n * paramL n := rfl
    have hq : (e - netE7 n) / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul (by omega)
    have hq1 : ((e - netE7 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    generalize (e - netE7 n) / (2 * paramJ n) = q at hq hq1 ⊢
    have : netV7 n = netV6 n + paramL1 n := by simp [netV6, netV7]; omega
    have : netV8 n = netV7 n + paramL n := rfl
    omega
  simp only [he8, ↓reduceIte]
  by_cases he9 : e < netE9 n
  · simp only [he9, ↓reduceIte]
    dsimp [endsB8]
    have : netE9 n = netE8 n + 2 * paramJ n * paramL n := rfl
    have hq : (e - netE8 n) / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul (by omega)
    have hj2 : ((e - netE8 n) / (2 * paramJ n)) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
    have : netV8 n = netV7 n + paramL n := rfl
    have : netV9 n = netV8 n + paramL2 n := rfl
    omega
  simp only [he9, ↓reduceIte]
  by_cases he10 : e < netE10 n
  · simp only [he10, ↓reduceIte]
    dsimp [endsB9]
    have : netE10 n = netE9 n + 2 * paramJ n * paramL n := rfl
    have hk : e - netE9 n < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
      calc e - netE9 n < 2 * paramJ n * paramL n := by omega
           _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by rw [hL_mul]; ring
    have hrem : (e - netE9 n) / (2 * paramJ n) < paramL2 n * paramL1 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
    have hj2 : ((e - netE9 n) / (2 * paramJ n)) / paramL1 n < paramL2 n :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : ((e - netE9 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    have : netV9 n = netV8 n + paramL2 n := rfl
    have : netV10 n = netV9 n + paramL1 n := rfl
    omega
  simp only [he10, ↓reduceIte]
  by_cases he11 : e < netE11 n
  · simp only [he11, ↓reduceIte]
    dsimp [endsB10]
    have : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
    have hq1 : ((e - netE10 n) / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    have : netV10 n = netV9 n + paramL1 n := rfl
    have : netV11 n = netV10 n + 2 * paramJ n * paramL n := rfl
    have : netV12 n = netV11 n + 2 * n := rfl
    split_ifs <;> omega
  simp only [he11, ↓reduceIte]
  by_cases he12 : e < netE12 n
  · simp only [he12, ↓reduceIte]
    dsimp [endsB11]
    have : netE12 n = netE11 n + 2 * n := rfl
    have hmod : (e - netE11 n) % n < n := Nat.mod_lt _ (by omega)
    have : netV12 n = netV11 n + 2 * n := rfl
    have : netV13 n = netV12 n + n := rfl
    omega
  simp only [he12, ↓reduceIte]
  by_cases he13 : e < netE13 n
  · simp only [he13, ↓reduceIte]
    dsimp [endsB12]
    set r := treeLog n + 1
    have : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl
    have hloc : e - netE12 n < treeEdgeOff r (r + 1) := by omega
    have hsp := decodeTreeEdge_spec hloc
    set t := decodeTreeEdge r (e - netE12 n)
    have hj1 : 1 ≤ t.1 := hsp.1
    have hjr : t.1 ≤ r := hsp.2.1
    have hnode : t.2.1 < 2 ^ (r - t.1) := hsp.2.2.1
    have hw : t.2.2 < 2 * t.1 + 1 := hsp.2.2.2.1
    have : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
    by_cases heven : t.2.2 % 2 = 0 ∧ t.2.2 < 2 * t.1
    · simp only [heven, and_self, ↓reduceIte]
      have hdst_lt := encodeTreeVert_lt hj1 hjr hnode (show 1 + t.2.2 / 2 < t.1 + 1 by omega)
      split_ifs <;> omega
    · simp only [show (t.2.2 % 2 = 0 ∧ t.2.2 < 2 * t.1) = False from eq_false heven, ↓reduceIte]
      set bitIdx := if t.2.2 = 2 * t.1 then t.1 else t.2.2 / 2
      have hbit : bitIdx ≤ t.1 := by dsimp [bitIdx]; split_ifs <;> omega
      by_cases hj_lt : t.1 < r
      · simp only [hj_lt, ↓reduceIte]
        have hstep : treeVertOff r (t.1 + 1) = treeVertOff r t.1 + (t.1 + 1) * 2 ^ (r - t.1) := by
          cases ht1 : t.1 with | zero => omega | succ _ => rfl
        have hmul : (t.2.1 + 1) * (t.1 + 1) ≤ 2 ^ (r - t.1) * (t.1 + 1) :=
          Nat.mul_le_mul_right _ hnode
        have hcomm : 2 ^ (r - t.1) * (t.1 + 1) = (t.1 + 1) * 2 ^ (r - t.1) := Nat.mul_comm _ _
        have hlin : (t.2.1 + 1) * (t.1 + 1) = t.2.1 * (t.1 + 1) + (t.1 + 1) := by ring
        have hparent_node : t.2.1 / 2 < 2 ^ (r - (t.1 + 1)) := by
          have hexp : 2 ^ (r - t.1) = 2 * 2 ^ (r - (t.1 + 1)) := by
            have : r - t.1 = (r - (t.1 + 1)) + 1 := by omega
            rw [this, pow_succ']
          exact Nat.div_lt_of_lt_mul (by omega)
        have hdst_lt : treeVertOff r (t.1 + 1) + (t.2.1 / 2) * (t.1 + 2) + (1 + bitIdx) <
            treeVertOff r (r + 1) :=
          encodeTreeVert_lt (r := r) (j := t.1 + 1) (node := t.2.1 / 2)
            (u := 1 + bitIdx) (by omega) (by omega) hparent_node (by omega)
        split_ifs <;> omega
      · simp only [hj_lt, ↓reduceIte]
        have hsrc_lt0 := encodeTreeVert_lt hj1 hjr hnode (u := 0) (by omega)
        have hsrc_lt1 := encodeTreeVert_lt hj1 hjr hnode (u := 1 + (t.2.2 - 1) / 2) (by omega)
        have : netV18 n = netV17 n + (r + 1) := rfl
        split_ifs <;> omega
  simp only [he13, ↓reduceIte]
  dsimp [endsB13]
  have : netEdgeCount n = netE13 n + (treeLog n + 3) := rfl
  have : netV17 n = netV16 n + 1 := rfl
  have : netV18 n = netV17 n + (treeLog n + 2) := rfl
  have : netVertCount n = netV18 n + 1 := rfl
  split_ifs <;> omega

def netEnds (n : ℕ) (e : Fin (netEdgeCount n)) :
    Fin (netVertCount n) × Fin (netVertCount n) :=
  let hb := rawEnds_lt_and_bound n e.val e.isLt
  (⟨(rawEnds n e.val).1, lt_trans hb.1 hb.2⟩, ⟨(rawEnds n e.val).2, hb.2⟩)

lemma netEnds_lt (n : ℕ) (e : Fin (netEdgeCount n)) :
    (netEnds n e).1.val < (netEnds n e).2.val :=
  (rawEnds_lt_and_bound n e.val e.isLt).1

lemma netNoLoop (n : ℕ) (e : Fin (netEdgeCount n)) :
    (netEnds n e).1 ≠ (netEnds n e).2 :=
  fun h => Nat.ne_of_lt (netEnds_lt n e) (congrArg Fin.val h)

lemma netEdgeCount_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ netEdgeCount n ∧ netEdgeCount n ≤ 420 * n := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · decide
  have hM1 : treeM n < 2 * n := treeM_lt_two_mul hn2
  have hr1_le : treeLog n ≤ n := treeLog_le_self hn2
  have hL : paramL n ≤ 3 * paramJ n := paramL_le_three_mul_paramJ hn
  have hJ2 : (paramJ n) ^ 2 < 9 * n := paramJ_sq_lt_nine_mul hn
  have hJL : 2 * paramJ n * paramL n < 54 * n := by
    calc
      2 * paramJ n * paramL n ≤ 2 * paramJ n * (3 * paramJ n) := Nat.mul_le_mul_left _ hL
      _ = 6 * (paramJ n) ^ 2 := by ring
      _ < 6 * (9 * n) := (Nat.mul_lt_mul_left (by decide)).2 hJ2
      _ = 54 * n := by ring
  have htree : treeEdgeOff (treeLog n + 1) (treeLog n + 2) < 20 * n := by
    have h1 : treeEdgeOff (treeLog n + 1) (treeLog n + 2) ≤ 5 * 2 ^ (treeLog n + 1) :=
      treeEdgeOff_total_le (r := treeLog n + 1) (by omega)
    have hpow : 2 ^ (treeLog n + 1) = 2 * treeM n := by unfold treeM; rw [pow_succ']
    omega
  simp only [netEdgeCount, netE13, netE12, netE11, netE10, netE9, netE8, netE7,
             netE6, netE5, netE4, netE3]
  constructor <;> omega

lemma netVertCount_le {n : ℕ} (hn : 1 ≤ n) :
    netVertCount n ≤ 280 * n := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · decide
  have hM1_lo : n ≤ treeM n := le_treeM n
  have hM1 : treeM n < 2 * n := treeM_lt_two_mul hn2
  have hr1_le : treeLog n ≤ n := treeLog_le_self hn2
  have hL : paramL n ≤ 3 * paramJ n := paramL_le_three_mul_paramJ hn
  have hJ1 : 1 ≤ paramJ n := one_le_paramJ n
  have hJ2 : (paramJ n) ^ 2 < 9 * n := paramJ_sq_lt_nine_mul hn
  have hJ_lt : paramJ n < 9 * n := by
    have : paramJ n ≤ (paramJ n) ^ 2 := by
      simpa using Nat.pow_le_pow_right hJ1 (show 1 ≤ 2 by decide)
    omega
  have hL_lt : paramL n < 27 * n := by omega
  have hL1_le : paramL1 n ≤ paramL n := by
    rw [paramL_eq_mul]; exact Nat.le_mul_of_pos_right _ (one_le_paramL2 n)
  have hL2_le : paramL2 n ≤ paramL n := by
    rw [paramL_eq_mul]; exact Nat.le_mul_of_pos_left _ (one_le_paramL1 n)
  have hJL : 2 * paramJ n * paramL n < 54 * n := by
    calc
      2 * paramJ n * paramL n ≤ 2 * paramJ n * (3 * paramJ n) := Nat.mul_le_mul_left _ hL
      _ = 6 * (paramJ n) ^ 2 := by ring
      _ < 6 * (9 * n) := (Nat.mul_lt_mul_left (by decide)).2 hJ2
      _ = 54 * n := by ring
  have htree : treeVertOff (treeLog n + 1) (treeLog n + 2) < 12 * n := by
    have h1 : treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ 3 * 2 ^ (treeLog n + 1) :=
      treeVertOff_total_le (r := treeLog n + 1) (by omega)
    have hpow : 2 ^ (treeLog n + 1) = 2 * treeM n := by unfold treeM; rw [pow_succ']
    omega
  simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12,
             netV11, netV10, netV9, netV8, netV7]
  omega

/-! ### Index Bijection Helpers & Exact `QCSD_incidentList` Characterization -/

lemma mul_add_div_mod {W q p : ℕ} (hW : 0 < W) (hp : p < W) :
    (q * W + p) / W = q ∧ (q * W + p) % W = p := by
  have hcomm : q * W = W * q := Nat.mul_comm q W
  rw [hcomm, Nat.mul_add_div hW, Nat.div_eq_of_lt hp, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  exact ⟨rfl, rfl⟩

lemma dftIdx_div_iff {W A B idx a : ℕ} (hW : 0 < W) (hA : 0 < A)
    (_ha : a < B) (hidx : idx < W * (A * B)) :
    (idx / W) / A = a ↔
      idx ∈ (List.range (W * A)).map (fun k => (a * A + k / W) * W + k % W) := by
  constructor
  · intro hdiv
    rw [List.mem_map]
    set q := (idx / W) % A
    set p := idx % W
    have hq : q < A := Nat.mod_lt _ hA
    have hp : p < W := Nat.mod_lt _ hW
    refine ⟨q * W + p, List.mem_range.mpr ?_, ?_⟩
    · have : q * W + p < (q + 1) * W := by
        have : (q + 1) * W = q * W + W := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm W A]; exact Nat.mul_le_mul_right W hq)
    · obtain ⟨hd, hm⟩ := mul_add_div_mod hW hp
      rw [hd, hm]
      have h1 : a * A + q = idx / W := by
        have hda := Nat.div_add_mod (idx / W) A
        have hc1 : A * ((idx / W) / A) = ((idx / W) / A) * A := Nat.mul_comm _ _
        rw [hdiv] at hc1 hda
        omega
      rw [h1]
      have h2 := Nat.div_add_mod idx W
      have hc2 : W * (idx / W) = (idx / W) * W := Nat.mul_comm _ _
      dsimp only [p]
      omega
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨k, hk, rfl⟩
    have hk' : k < A * W := by rw [Nat.mul_comm]; exact List.mem_range.mp hk
    have hkw : k / W < A := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk')
    have hkm : k % W < W := Nat.mod_lt k hW
    obtain ⟨hd1, _⟩ := mul_add_div_mod hW hkm
    obtain ⟨hd2, _⟩ := mul_add_div_mod hA hkw
    rw [hd1, hd2]

lemma dftIdx_mod_left_iff {W A B idx b : ℕ} (hW : 0 < W) (hA : 0 < A)
    (hb : b < A) (hidx : idx < W * (A * B)) :
    (idx / W) % A = b ↔
      idx ∈ (List.range (W * B)).map (fun k => ((k / W) * A + b) * W + k % W) := by
  constructor
  · intro hmod
    rw [List.mem_map]
    have hrem : idx / W < B * A := by
      have hlt_mul : idx < (B * A) * W := by
        calc
          idx < W * (A * B) := hidx
          _ = (B * A) * W := by ring
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt_mul)
    set q := (idx / W) / A
    set p := idx % W
    have hq : q < B := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hp : p < W := Nat.mod_lt _ hW
    refine ⟨q * W + p, List.mem_range.mpr ?_, ?_⟩
    · have : q * W + p < (q + 1) * W := by
        have : (q + 1) * W = q * W + W := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm W B]; exact Nat.mul_le_mul_right W hq)
    · obtain ⟨hd, hm⟩ := mul_add_div_mod hW hp
      rw [hd, hm]
      have h1 : q * A + b = idx / W := by
        have hda := Nat.div_add_mod (idx / W) A
        have hc1 : A * q = q * A := Nat.mul_comm _ _
        dsimp only [q] at hc1 ⊢
        omega
      rw [h1]
      have h2 := Nat.div_add_mod idx W
      have hc2 : W * (idx / W) = (idx / W) * W := Nat.mul_comm _ _
      dsimp only [p]
      omega
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨k, _, rfl⟩
    have hkm : k % W < W := Nat.mod_lt k hW
    obtain ⟨hd1, _⟩ := mul_add_div_mod hW hkm
    obtain ⟨_, hm2⟩ := mul_add_div_mod hA hb
    rw [hd1, hm2]

lemma dftIdx_mod_right_iff {W A B idx b : ℕ} (hW : 0 < W) (hA : 0 < A)
    (hb : b < A) (hidx : idx < W * (A * B)) :
    (idx / W) % A = b ↔
      idx ∈ (List.range (W * B)).map (fun k => (b + A * (k / W)) * W + k % W) := by
  rw [dftIdx_mod_left_iff hW hA hb hidx]
  have hfn : (fun k => ((k / W) * A + b) * W + k % W) =
      (fun k => (b + A * (k / W)) * W + k % W) := by
    funext k; ring
  rw [hfn]

def ovlInLocal (J L tk : ℕ) : List ℕ :=
  (if 0 < tk / J ∧ tk / J - 1 < L then [(tk / J - 1) * (2 * J) + (J + tk % J)] else []) ++
  (if tk / J < L then [(tk / J) * (2 * J) + tk % J] else [])

lemma ovlTargetBit_eq_iff {J L k tk : ℕ} (hJ : 0 < J) (hk : k < 2 * J * L) :
    ovlTargetBit J (k / (2 * J)) (k % (2 * J)) = tk ↔ k ∈ ovlInLocal J L tk := by
  set blk := k / (2 * J)
  set p := k % (2 * J)
  have hblk : blk < L := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
  have hp : p < 2 * J := Nat.mod_lt k (by omega)
  have hk_eq : k = blk * (2 * J) + p := by
    have := Nat.div_add_mod k (2 * J)
    have hc : (2 * J) * blk = blk * (2 * J) := Nat.mul_comm _ _
    dsimp only [blk, p] at hc ⊢
    omega
  unfold ovlTargetBit ovlInLocal
  rw [List.mem_append]
  have htk_mod : tk % J < J := Nat.mod_lt tk hJ
  constructor
  · intro heq
    by_cases hpJ : p < J
    · simp only [hpJ, ↓reduceIte] at heq
      subst heq
      obtain ⟨hd, hm⟩ := mul_add_div_mod (q := blk) hJ hpJ
      right
      simp only [hd, hm, hblk, ↓reduceIte, List.mem_singleton]
      exact hk_eq
    · simp only [hpJ, ↓reduceIte] at heq
      subst heq
      have hpJ' : p - J < J := by omega
      obtain ⟨hd, hm⟩ := mul_add_div_mod (q := blk + 1) hJ hpJ'
      left
      rw [hd, hm, Nat.add_sub_cancel]
      have hpos : 0 < blk + 1 := Nat.succ_pos _
      simp only [hpos, hblk, and_self, ↓reduceIte, List.mem_singleton]
      rw [hk_eq]
      omega
  · rintro (hhi | hlo)
    · split_ifs at hhi with hcond
      · simp only [List.mem_singleton] at hhi
        obtain ⟨hd_k, hm_k⟩ := mul_add_div_mod (W := 2 * J) (q := tk / J - 1) (p := J + tk % J)
          (by omega) (by omega)
        have hb_eq : blk = tk / J - 1 := by dsimp [blk]; rw [hhi, hd_k]
        have hp_eq : p = J + tk % J := by dsimp [p]; rw [hhi, hm_k]
        have hnp : ¬(J + tk % J < J) := by omega
        simp only [hp_eq, hb_eq, hnp, ↓reduceIte]
        have hdm := Nat.div_add_mod tk J
        have hc : J * (tk / J) = (tk / J) * J := Nat.mul_comm _ _
        have hsub : (tk / J - 1 + 1) * J = (tk / J) * J := by congr 1; omega
        omega
      · simp at hhi
    · split_ifs at hlo with hcond
      · simp only [List.mem_singleton] at hlo
        obtain ⟨hd_k, hm_k⟩ := mul_add_div_mod (W := 2 * J) (q := tk / J) (p := tk % J)
          (by omega) (by omega)
        have hb_eq : blk = tk / J := by dsimp [blk]; rw [hlo, hd_k]
        have hp_eq : p = tk % J := by dsimp [p]; rw [hlo, hm_k]
        simp only [hp_eq, hb_eq, htk_mod, ↓reduceIte]
        have hdm := Nat.div_add_mod tk J
        have hc : J * (tk / J) = (tk / J) * J := Nat.mul_comm _ _
        omega
      · simp at hlo

def sumWireLoc (j' b : ℕ) : ℕ :=
  if b = j' then 2 * j' else 2 * b + 1

lemma sumWireLoc_lt {j' b : ℕ} (_hb : b ≤ j') : sumWireLoc j' b < 2 * j' + 1 := by
  unfold sumWireLoc; split_ifs <;> omega

lemma sumWireLoc_iff {j' w b : ℕ} (_hj' : 1 ≤ j') (hw : w < 2 * j' + 1) (_hb : b ≤ j') :
    (¬(w % 2 = 0 ∧ w < 2 * j') ∧ (if w = 2 * j' then j' else w / 2) = b) ↔
      w = sumWireLoc j' b := by
  unfold sumWireLoc
  split_ifs <;> omega

/-! ### Explicit Incoming & Outgoing Edge Lists (`inEdges`, `outEdges`, `expectedInc`) -/

def inEdges (n v : ℕ) : List ℕ :=
  let J := paramJ n
  let L := paramL n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let r := treeLog n + 1
  if v < netV1 n then []
  else if v < netV2 n then [netE0 n + (v - netV1 n)]
  else if v < netV3 n then []
  else if v < netV4 n then
    (fwdSt1InIndices n J L2 (v - netV3 n)).map (fun idx => netE3 n + idx)
  else if v < netV5 n then
    let q1 := v - netV4 n
    (List.range (2 * J * L2)).map
      (fun k => netE4 n + ((k / (2 * J)) * L1 + q1) * (2 * J) + k % (2 * J))
  else if v < netV6 n then
    (fwdSt1InIndices n J L2 (v - netV5 n)).map (fun idx => netE1 n + n + idx)
  else if v < netV7 n then
    let q1 := v - netV6 n
    (List.range (2 * J * L2)).map
      (fun k => netE6 n + ((k / (2 * J)) * L1 + q1) * (2 * J) + k % (2 * J))
  else if v < netV8 n then
    let q := v - netV7 n
    (List.range (2 * J)).map (fun p => netE5 n + q * (2 * J) + p) ++
    (List.range (2 * J)).map (fun p => netE7 n + q * (2 * J) + p)
  else if v < netV9 n then
    let j2 := v - netV8 n
    (List.range (2 * J * L1)).map
      (fun k => netE8 n + (L2 * (k / (2 * J)) + j2) * (2 * J) + k % (2 * J))
  else if v < netV10 n then
    let q1 := v - netV9 n
    (List.range (2 * J * L2)).map
      (fun k => netE9 n + ((k / (2 * J)) * L1 + q1) * (2 * J) + k % (2 * J))
  else if v < netV11 n then
    let k := v - netV10 n
    if ovlTargetBit J (k / (2 * J)) (k % (2 * J)) < 2 * n then [] else [netE10 n + k]
  else if v < netV12 n then
    (ovlInLocal J L (v - netV11 n)).map (fun k => netE10 n + k)
  else if v < netV13 n then
    let i := v - netV12 n
    [netE1 n + i, netE11 n + i, netE11 n + i + n]
  else if v < netV14 n then []
  else if v < netV15 n then []
  else if v < netV16 n then
    let tv := decodeTreeVert r (v - netV15 n)
    let j := tv.1; let node := tv.2.1; let u := tv.2.2
    if u = 0 then []
    else
      let b := u - 1
      let cinE := netE12 n + treeEdgeOff r j + node * (2 * j + 1) + 2 * b
      if j = 1 then
        [netE2 n + 2 * node, netE2 n + 2 * node + 1, cinE]
      else
        let j' := j - 1
        let sw := sumWireLoc j' b
        [netE12 n + treeEdgeOff r j' + (2 * node) * (2 * j' + 1) + sw,
         netE12 n + treeEdgeOff r j' + (2 * node + 1) * (2 * j' + 1) + sw,
         cinE]
  else if v < netV17 n then []
  else if v < netV18 n then
    let b := v - netV17 n
    [netE12 n + treeEdgeOff r r + sumWireLoc r b, netE13 n + b]
  else [netE13 n + (treeLog n + 2)]

def outEdges (n v : ℕ) : List ℕ :=
  let J := paramJ n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let r := treeLog n + 1
  if v < netV1 n then [netE0 n + v]
  else if v < netV2 n then
    let i := v - netV1 n
    [netE1 n + i, netE2 n + (if i < n then i else treeM n + (i - n))]
  else if v < netV3 n then [netE3 n + (v - netV2 n)]
  else if v < netV4 n then
    let j2 := v - netV3 n
    (List.range (2 * J * L1)).map
      (fun k => netE4 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
  else if v < netV5 n then
    let q1 := v - netV4 n
    (List.range (2 * J * L2)).map
      (fun k => netE5 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J))
  else if v < netV6 n then
    let j2 := v - netV5 n
    (List.range (2 * J * L1)).map
      (fun k => netE6 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
  else if v < netV7 n then
    let q1 := v - netV6 n
    (List.range (2 * J * L2)).map
      (fun k => netE7 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J))
  else if v < netV8 n then
    let q := v - netV7 n
    (List.range (2 * J)).map (fun p => netE8 n + q * (2 * J) + p)
  else if v < netV9 n then
    let j2 := v - netV8 n
    (List.range (2 * J * L1)).map
      (fun k => netE9 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
  else if v < netV10 n then
    let q1 := v - netV9 n
    (List.range (2 * J * L2)).map
      (fun k => netE10 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J))
  else if v < netV11 n then []
  else if v < netV12 n then [netE11 n + (v - netV11 n)]
  else if v < netV13 n then []
  else if v < netV14 n then [netE2 n + n + (v - netV13 n)]
  else if v < netV15 n then [netE2 n + treeM n + n + (v - netV14 n)]
  else if v < netV16 n then
    let tv := decodeTreeVert r (v - netV15 n)
    let j := tv.1; let node := tv.2.1; let u := tv.2.2
    let base := netE12 n + treeEdgeOff r j + node * (2 * j + 1)
    if u = 0 then [base]
    else [base + 2 * (u - 1) + 1, base + 2 * (u - 1) + 2]
  else if v < netV17 n then [netE13 n]
  else if v < netV18 n then [netE13 n + (v - netV17 n) + 1]
  else []

def expectedInc (n v : ℕ) : List ℕ :=
  inEdges n v ++ outEdges n v

/-! ### Edge Chain, Block Selectors, and Pairwise Helpers -/

lemma netE_chain (n : ℕ) :
    netE0 n ≤ netE1 n ∧ netE1 n ≤ netE2 n ∧ netE2 n ≤ netE3 n ∧ netE3 n ≤ netE4 n ∧
    netE4 n ≤ netE5 n ∧ netE5 n ≤ netE6 n ∧ netE6 n ≤ netE7 n ∧ netE7 n ≤ netE8 n ∧
    netE8 n ≤ netE9 n ∧ netE9 n ≤ netE10 n ∧ netE10 n ≤ netE11 n ∧ netE11 n ≤ netE12 n ∧
    netE12 n ≤ netE13 n ∧ netE13 n < netEdgeCount n := by
  simp only [netE0, netE1, netE2, netE3, netE4, netE5, netE6, netE7, netE8, netE9,
             netE10, netE11, netE12, netE13, netEdgeCount]
  omega

lemma rawEnds_of_B0 {n e : ℕ} (hhi : e < netE1 n) : rawEnds n e = endsB0 n e := by
  unfold rawEnds; simp only [hhi, ↓reduceIte]

lemma rawEnds_of_B1 {n e : ℕ} (hlo : netE1 n ≤ e) (hhi : e < netE2 n) :
    rawEnds n e = endsB1 n (e - netE1 n) := by
  have h1 : ¬ e < netE1 n := by omega
  unfold rawEnds; simp only [h1, hhi, ↓reduceIte]

lemma rawEnds_of_B2 {n e : ℕ} (hlo : netE2 n ≤ e) (hhi : e < netE3 n) :
    rawEnds n e = endsB2 n (e - netE2 n) := by
  rcases netE_chain n with ⟨_, h12, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  unfold rawEnds; simp only [h1, h2, hhi, ↓reduceIte]

lemma rawEnds_of_B3 {n e : ℕ} (hlo : netE3 n ≤ e) (hhi : e < netE4 n) :
    rawEnds n e = endsB3 n (e - netE3 n) := by
  rcases netE_chain n with ⟨_, h12, h23, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, hhi, ↓reduceIte]

lemma rawEnds_of_B4 {n e : ℕ} (hlo : netE4 n ≤ e) (hhi : e < netE5 n) :
    rawEnds n e = endsB4 n (e - netE4 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, hhi, ↓reduceIte]

lemma rawEnds_of_B5 {n e : ℕ} (hlo : netE5 n ≤ e) (hhi : e < netE6 n) :
    rawEnds n e = endsB5 n (e - netE5 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, hhi, ↓reduceIte]

lemma rawEnds_of_B6 {n e : ℕ} (hlo : netE6 n ≤ e) (hhi : e < netE7 n) :
    rawEnds n e = endsB6 n (e - netE6 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, hhi, ↓reduceIte]

lemma rawEnds_of_B7 {n e : ℕ} (hlo : netE7 n ≤ e) (hhi : e < netE8 n) :
    rawEnds n e = endsB7 n (e - netE7 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, hhi, ↓reduceIte]

lemma rawEnds_of_B8 {n e : ℕ} (hlo : netE8 n ≤ e) (hhi : e < netE9 n) :
    rawEnds n e = endsB8 n (e - netE8 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, hhi, ↓reduceIte]

lemma rawEnds_of_B9 {n e : ℕ} (hlo : netE9 n ≤ e) (hhi : e < netE10 n) :
    rawEnds n e = endsB9 n (e - netE9 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  have h9 : ¬ e < netE9 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hhi, ↓reduceIte]

lemma rawEnds_of_B10 {n e : ℕ} (hlo : netE10 n ≤ e) (hhi : e < netE11 n) :
    rawEnds n e = endsB10 n (e - netE10 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  have h9 : ¬ e < netE9 n := by omega
  have h10 : ¬ e < netE10 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hhi, ↓reduceIte]

lemma rawEnds_of_B11 {n e : ℕ} (hlo : netE11 n ≤ e) (hhi : e < netE12 n) :
    rawEnds n e = endsB11 n (e - netE11 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  have h9 : ¬ e < netE9 n := by omega
  have h10 : ¬ e < netE10 n := by omega
  have h11 : ¬ e < netE11 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hhi, ↓reduceIte]

lemma rawEnds_of_B12 {n e : ℕ} (hlo : netE12 n ≤ e) (hhi : e < netE13 n) :
    rawEnds n e = endsB12 n (e - netE12 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  have h9 : ¬ e < netE9 n := by omega
  have h10 : ¬ e < netE10 n := by omega
  have h11 : ¬ e < netE11 n := by omega
  have h12' : ¬ e < netE12 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12', hhi, ↓reduceIte]

lemma rawEnds_of_B13 {n e : ℕ} (hlo : netE13 n ≤ e) :
    rawEnds n e = endsB13 n (e - netE13 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, h1213, _⟩
  have h1 : ¬ e < netE1 n := by omega
  have h2 : ¬ e < netE2 n := by omega
  have h3 : ¬ e < netE3 n := by omega
  have h4 : ¬ e < netE4 n := by omega
  have h5 : ¬ e < netE5 n := by omega
  have h6 : ¬ e < netE6 n := by omega
  have h7 : ¬ e < netE7 n := by omega
  have h8 : ¬ e < netE8 n := by omega
  have h9 : ¬ e < netE9 n := by omega
  have h10 : ¬ e < netE10 n := by omega
  have h11 : ¬ e < netE11 n := by omega
  have h12' : ¬ e < netE12 n := by omega
  have h13' : ¬ e < netE13 n := by omega
  unfold rawEnds; simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12', h13', ↓reduceIte]

lemma pairwise_lt_range : ∀ m : ℕ, (List.range m).Pairwise (· < ·)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨pairwise_lt_range m, List.pairwise_singleton _ _,
      fun x hx y hy => by simp at hx hy; omega⟩

lemma pairwise_lt_filter {l : List ℕ} (p : ℕ → Bool) (h : l.Pairwise (· < ·)) :
    (l.filter p).Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.pairwise_cons] at h
    simp only [List.filter_cons]
    split_ifs
    · rw [List.pairwise_cons]
      exact ⟨fun x hx => h.1 x (List.mem_of_mem_filter hx), ih h.2⟩
    · exact ih h.2

lemma pairwise_lt_map {l : List ℕ} {B : ℕ} (f : ℕ → ℕ)
    (hl : l.Pairwise (· < ·)) (hb : ∀ x ∈ l, x < B)
    (hmono : ∀ i j, i < j → j < B → f i < f j) :
    (l.map f).Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, ih hl.2 (fun x hx => hb x (List.mem_cons_of_mem a hx))⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmono a x (hl.1 x hx) (hb x (List.mem_cons_of_mem a hx))

lemma pairwise_lt_append {l1 l2 : List ℕ}
    (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (hsep : ∀ x ∈ l1, ∀ y ∈ l2, x < y) :
    (l1 ++ l2).Pairwise (· < ·) :=
  List.pairwise_append.mpr ⟨h1, h2, hsep⟩

lemma pairwise_lt_two {a b : ℕ} (hab : a < b) : [a, b].Pairwise (· < ·) := by
  simp [hab]

lemma pairwise_lt_three {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    [a, b, c].Pairwise (· < ·) := by
  simp [hab, hbc, Nat.lt_trans hab hbc]

lemma affine_contig_eq {W c k : ℕ} :
    (c + k / W) * W + k % W = c * W + k := by
  have h1 : (c + k / W) * W = c * W + (k / W) * W := Nat.add_mul _ _ _
  have h2 := Nat.div_add_mod k W
  have h3 : W * (k / W) = (k / W) * W := Nat.mul_comm _ _
  omega

lemma affine_contig_lt {W A B c k : ℕ} (hc : c < B) (hk : k < W * A) :
    (c * A + k / W) * W + k % W < W * (A * B) := by
  rw [affine_contig_eq]
  have h1 : (c + 1) * (A * W) ≤ B * (A * W) := Nat.mul_le_mul_right _ hc
  have h2 : (c + 1) * (A * W) = c * A * W + A * W := by ring
  have h3 : B * (A * W) = W * (A * B) := by ring
  have h4 : W * A = A * W := Nat.mul_comm _ _
  omega

lemma affine_stride_strictMono {W A b k1 k2 : ℕ}
    (hW : 0 < W) (hA : 1 ≤ A) (hk : k1 < k2) :
    ((k1 / W) * A + b) * W + k1 % W < ((k2 / W) * A + b) * W + k2 % W := by
  set q1 := k1 / W; set p1 := k1 % W
  set q2 := k2 / W; set p2 := k2 % W
  have hp1 : p1 < W := Nat.mod_lt k1 hW
  have hp2 : p2 < W := Nat.mod_lt k2 hW
  have hd1 := Nat.div_add_mod k1 W
  have hd2 := Nat.div_add_mod k2 W
  have hc1 : W * q1 = q1 * W := Nat.mul_comm _ _
  have hc2 : W * q2 = q2 * W := Nat.mul_comm _ _
  have hq_le : q1 ≤ q2 := Nat.div_le_div_right (le_of_lt hk)
  rcases eq_or_lt_of_le hq_le with hq_eq | hq_lt
  · have hp_lt : p1 < p2 := by
      dsimp only [q1, p1, q2, p2] at hq_eq hc1 hc2 ⊢
      rw [hc1] at hd1
      rw [hc2, ← hq_eq] at hd2
      omega
    rw [hq_eq]
    omega
  · have hstep : (q1 * A + b + 1) * W ≤ (q2 * A + b) * W := by
      apply Nat.mul_le_mul_right W
      have : (q1 + 1) * A ≤ q2 * A := Nat.mul_le_mul_right A hq_lt
      have : (q1 + 1) * A = q1 * A + A := by ring
      omega
    have hlin : (q1 * A + b + 1) * W = (q1 * A + b) * W + W := by ring
    omega

lemma affine_stride_lt {W A B b k : ℕ}
    (hW : 0 < W) (hb : b < A) (hk : k < W * B) :
    ((k / W) * A + b) * W + k % W < W * (A * B) := by
  have hk' : k < B * W := by simpa [Nat.mul_comm] using hk
  have hq : k / W < B := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk')
  have hp : k % W < W := Nat.mod_lt k hW
  have h1 : (k / W) * A + b + 1 ≤ B * A := by
    have : (k / W + 1) * A ≤ B * A := Nat.mul_le_mul_right A hq
    have : (k / W + 1) * A = (k / W) * A + A := by ring
    omega
  have h2 : ((k / W) * A + b + 1) * W ≤ (B * A) * W := Nat.mul_le_mul_right W h1
  have hlin : ((k / W) * A + b + 1) * W = ((k / W) * A + b) * W + W := by ring
  have h3 : (B * A) * W = W * (A * B) := by ring
  omega

lemma ovlInLocal_spec {J L tk : ℕ} (hJ : 0 < J) :
    (ovlInLocal J L tk).Pairwise (· < ·) ∧ ∀ k ∈ ovlInLocal J L tk, k < 2 * J * L := by
  unfold ovlInLocal
  have hmod : tk % J < J := Nat.mod_lt tk hJ
  have hhi_lt : 0 < tk / J ∧ tk / J - 1 < L →
      (tk / J - 1) * (2 * J) + (J + tk % J) < 2 * J * L := by
    rintro ⟨_, hlt⟩
    have h1 : (tk / J - 1 + 1) * (2 * J) ≤ L * (2 * J) := Nat.mul_le_mul_right _ hlt
    have h2 : (tk / J - 1 + 1) * (2 * J) = (tk / J - 1) * (2 * J) + 2 * J := by ring
    have h3 : L * (2 * J) = 2 * J * L := by ring
    omega
  have hlo_lt : tk / J < L → (tk / J) * (2 * J) + tk % J < 2 * J * L := by
    intro hlt
    have h1 : (tk / J + 1) * (2 * J) ≤ L * (2 * J) := Nat.mul_le_mul_right _ hlt
    have h2 : (tk / J + 1) * (2 * J) = (tk / J) * (2 * J) + 2 * J := by ring
    have h3 : L * (2 * J) = 2 * J * L := by ring
    omega
  constructor
  · apply pairwise_lt_append
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro x hx y hy
      split_ifs at hx with h1
      · split_ifs at hy with h2
        · simp only [List.mem_singleton] at hx hy
          subst hx; subst hy
          have heq : (tk / J - 1 + 1) * (2 * J) = (tk / J) * (2 * J) := by congr 1; omega
          have hlin : (tk / J - 1 + 1) * (2 * J) = (tk / J - 1) * (2 * J) + 2 * J := by ring
          omega
        · simp at hy
      · simp at hx
  · intro k hk
    rw [List.mem_append] at hk
    rcases hk with hk | hk
    · split_ifs at hk with h1
      · simp only [List.mem_singleton] at hk; subst hk; exact hhi_lt h1
      · simp at hk
    · split_ifs at hk with h2
      · simp only [List.mem_singleton] at hk; subst hk; exact hlo_lt h2
      · simp at hk

/-! ### Full `inOutEdges_spec` and Reverse Membership Lemmas -/

lemma endsB12_of_decode {n locE j node w : ℕ}
    (h : decodeTreeEdge (treeLog n + 1) locE = (j, node, w)) :
    endsB12 n locE =
      (if w = 0 then netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1)
       else netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) + 1 + (w - 1) / 2,
       if w % 2 = 0 ∧ w < 2 * j then
         netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) + 1 + w / 2
       else
         let bitIdx := if w = 2 * j then j else w / 2
         if j < treeLog n + 1 then
           netV15 n + treeVertOff (treeLog n + 1) (j + 1) + (node / 2) * (j + 2) + 1 + bitIdx
         else netV17 n + bitIdx) := by
  unfold endsB12; dsimp only; rw [h]

lemma inEdges_of_V15 {n v j node u : ℕ}
    (hlo : netV15 n ≤ v) (hhi : v < netV16 n)
    (hdec : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (j, node, u)) :
    inEdges n v =
      if u = 0 then []
      else
        let r := treeLog n + 1
        let b := u - 1
        let cinE := netE12 n + treeEdgeOff r j + node * (2 * j + 1) + 2 * b
        if j = 1 then [netE2 n + 2 * node, netE2 n + 2 * node + 1, cinE]
        else
          let j' := j - 1
          let sw := sumWireLoc j' b
          [netE12 n + treeEdgeOff r j' + (2 * node) * (2 * j' + 1) + sw,
           netE12 n + treeEdgeOff r j' + (2 * node + 1) * (2 * j' + 1) + sw,
           cinE] := by
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, hhi, ↓reduceIte, hdec]

lemma outEdges_of_V15 {n v j node u : ℕ}
    (hlo : netV15 n ≤ v) (hhi : v < netV16 n)
    (hdec : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (j, node, u)) :
    outEdges n v =
      let r := treeLog n + 1
      let base := netE12 n + treeEdgeOff r j + node * (2 * j + 1)
      if u = 0 then [base]
      else [base + 2 * (u - 1) + 1, base + 2 * (u - 1) + 2] := by
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, hhi, ↓reduceIte, hdec]

lemma inOut_of_V0 {n v : ℕ} (hhi : v < netV1 n) :
    inEdges n v = [] ∧ outEdges n v = [netE0 n + v] := by
  unfold inEdges outEdges; dsimp only; simp only [hhi, ↓reduceIte]; trivial

lemma inOut_of_V1 {n v : ℕ} (hlo : netV1 n ≤ v) (hhi : v < netV2 n) :
    inEdges n v = [netE0 n + (v - netV1 n)] ∧
    outEdges n v = [netE1 n + (v - netV1 n),
      netE2 n + (if v - netV1 n < n then v - netV1 n else treeM n + (v - netV1 n - n))] := by
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, hhi, ↓reduceIte]; trivial

lemma inOut_of_V2 {n v : ℕ} (hlo : netV2 n ≤ v) (hhi : v < netV3 n) :
    inEdges n v = [] ∧ outEdges n v = [netE3 n + (v - netV2 n)] := by
  rcases netV_chain n with ⟨_, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V3 {n v : ℕ} (hlo : netV3 n ≤ v) (hhi : v < netV4 n) :
    inEdges n v = (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)).map (fun idx => netE3 n + idx) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL1 n)).map
      (fun k => netE4 n + ((v - netV3 n) * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V4 {n v : ℕ} (hlo : netV4 n ≤ v) (hhi : v < netV5 n) :
    inEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE4 n + ((k / (2 * paramJ n)) * paramL1 n + (v - netV4 n)) * (2 * paramJ n) + k % (2 * paramJ n)) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE5 n + ((v - netV4 n) + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V5 {n v : ℕ} (hlo : netV5 n ≤ v) (hhi : v < netV6 n) :
    inEdges n v = (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)).map (fun idx => netE1 n + n + idx) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL1 n)).map
      (fun k => netE6 n + ((v - netV5 n) * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V6 {n v : ℕ} (hlo : netV6 n ≤ v) (hhi : v < netV7 n) :
    inEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE6 n + ((k / (2 * paramJ n)) * paramL1 n + (v - netV6 n)) * (2 * paramJ n) + k % (2 * paramJ n)) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE7 n + ((v - netV6 n) + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V7 {n v : ℕ} (hlo : netV7 n ≤ v) (hhi : v < netV8 n) :
    inEdges n v =
      (List.range (2 * paramJ n)).map (fun p => netE5 n + (v - netV7 n) * (2 * paramJ n) + p) ++
      (List.range (2 * paramJ n)).map (fun p => netE7 n + (v - netV7 n) * (2 * paramJ n) + p) ∧
    outEdges n v = (List.range (2 * paramJ n)).map (fun p => netE8 n + (v - netV7 n) * (2 * paramJ n) + p) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V8 {n v : ℕ} (hlo : netV8 n ≤ v) (hhi : v < netV9 n) :
    inEdges n v = (List.range (2 * paramJ n * paramL1 n)).map
      (fun k => netE8 n + (paramL2 n * (k / (2 * paramJ n)) + (v - netV8 n)) * (2 * paramJ n) + k % (2 * paramJ n)) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL1 n)).map
      (fun k => netE9 n + ((v - netV8 n) * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V9 {n v : ℕ} (hlo : netV9 n ≤ v) (hhi : v < netV10 n) :
    inEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE9 n + ((k / (2 * paramJ n)) * paramL1 n + (v - netV9 n)) * (2 * paramJ n) + k % (2 * paramJ n)) ∧
    outEdges n v = (List.range (2 * paramJ n * paramL2 n)).map
      (fun k => netE10 n + ((v - netV9 n) + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V10 {n v : ℕ} (hlo : netV10 n ≤ v) (hhi : v < netV11 n) :
    inEdges n v =
      (let k := v - netV10 n
       if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
       then [] else [netE10 n + k]) ∧
    outEdges n v = [] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V11 {n v : ℕ} (hlo : netV11 n ≤ v) (hhi : v < netV12 n) :
    inEdges n v = (ovlInLocal (paramJ n) (paramL n) (v - netV11 n)).map (fun k => netE10 n + k) ∧
    outEdges n v = [netE11 n + (v - netV11 n)] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V12 {n v : ℕ} (hlo : netV12 n ≤ v) (hhi : v < netV13 n) :
    inEdges n v = [netE1 n + (v - netV12 n), netE11 n + (v - netV12 n), netE11 n + (v - netV12 n) + n] ∧
    outEdges n v = [] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V13 {n v : ℕ} (hlo : netV13 n ≤ v) (hhi : v < netV14 n) :
    inEdges n v = [] ∧ outEdges n v = [netE2 n + n + (v - netV13 n)] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V14 {n v : ℕ} (hlo : netV14 n ≤ v) (hhi : v < netV15 n) :
    inEdges n v = [] ∧ outEdges n v = [netE2 n + treeM n + n + (v - netV14 n)] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V16 {n v : ℕ} (hlo : netV16 n ≤ v) (hhi : v < netV17 n) :
    inEdges n v = [] ∧ outEdges n v = [netE13 n] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V17 {n v : ℕ} (hlo : netV17 n ≤ v) (hhi : v < netV18 n) :
    inEdges n v = [netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 1) + sumWireLoc (treeLog n + 1) (v - netV17 n),
                   netE13 n + (v - netV17 n)] ∧
    outEdges n v = [netE13 n + (v - netV17 n) + 1] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, hhi, ↓reduceIte]
  trivial

lemma inOut_of_V18 {n v : ℕ} (hlo : netV18 n ≤ v) :
    inEdges n v = [netE13 n + (treeLog n + 2)] ∧ outEdges n v = [] := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold inEdges outEdges; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, show ¬(v < netV18 n) by omega, ↓reduceIte]
  trivial

def InOutSpecProp (n v : ℕ) : Prop :=
  (inEdges n v).Pairwise (· < ·) ∧
  (outEdges n v).Pairwise (· < ·) ∧
  (∀ e1 ∈ inEdges n v, ∀ e2 ∈ outEdges n v, e1 < e2) ∧
  (∀ e ∈ inEdges n v, e < netEdgeCount n ∧ (rawEnds n e).2 = v) ∧
  (∀ e ∈ outEdges n v, e < netEdgeCount n ∧ (rawEnds n e).1 = v)

lemma inOutEdges_spec_0_5 (n v : ℕ) (hv6 : v < netV6 n) : InOutSpecProp n v := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netV_chain n with
    ⟨hv0, hv1_le, hv2_le, hv3_le, hv4_le, hv5_le, hv6_le, hv7_le, hv8_le, hv9_le,
     hv10_le, hv11_le, hv12_le, hv13_le, hv14_le, hv15_le, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with
    ⟨he0_le, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  unfold InOutSpecProp
  by_cases hv1 : v < netV1 n
  · rw [(inOut_of_V0 hv1).1, (inOut_of_V0 hv1).2]
    have hV1 : netV1 n = 2 * n := rfl; have hE0 : netE0 n = 0 := rfl; have hE1 : netE1 n = 2 * n := rfl
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    refine ⟨by omega, ?_⟩; rw [rawEnds_of_B0 (by omega)]; dsimp [endsB0, netV0]; omega
  by_cases hv2 : v < netV2 n
  · rw [(inOut_of_V1 (by omega) hv2).1, (inOut_of_V1 (by omega) hv2).2]
    have hV1 : netV1 n = 2 * n := rfl; have hV2 : netV2 n = 4 * n := rfl
    have hE0 : netE0 n = 0 := rfl; have hE1 : netE1 n = 2 * n := rfl
    have hE2 : netE2 n = 4 * n := rfl; have hE3 : netE3 n = 4 * n + 2 * treeM n := rfl
    set i := v - netV1 n
    have hi : i < 2 * n := by omega
    set leaf := if i < n then i else treeM n + (i - n)
    have hleaf : leaf < 2 * treeM n := by dsimp [leaf]; split_ifs <;> omega
    refine ⟨by simp, pairwise_lt_two (by omega), ?_, ?_, ?_⟩
    · intro e1 he1 e2 he2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he1 he2
      rcases he2 with rfl | rfl <;> omega
    · intro e he; simp only [List.mem_singleton] at he; subst he
      refine ⟨by omega, ?_⟩; rw [rawEnds_of_B0 (by omega)]; dsimp [endsB0]; omega
    · intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · refine ⟨by omega, ?_⟩
        rw [rawEnds_of_B1 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB1]; omega
      · refine ⟨by omega, ?_⟩
        rw [rawEnds_of_B2 (by omega) (by omega), Nat.add_sub_cancel_left]
        dsimp [endsB2, leaf]; split_ifs <;> omega
  by_cases hv3 : v < netV3 n
  · rw [(inOut_of_V2 (by omega) hv3).1, (inOut_of_V2 (by omega) hv3).2]
    have hV2 : netV2 n = 4 * n := rfl; have hV3 : netV3 n = 5 * n := rfl
    have hE4 : netE4 n = netE3 n + n := rfl
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B3 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB3]; omega
  by_cases hv4 : v < netV4 n
  · rw [(inOut_of_V3 (by omega) hv4).1, (inOut_of_V3 (by omega) hv4).2]
    have hV4 : netV4 n = netV3 n + paramL2 n := by simp [netV3, netV4]
    have hE4 : netE4 n = netE3 n + n := rfl
    have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
    set j2 := v - netV3 n
    have hj2 : j2 < paramL2 n := by omega
    have hin_spec : ∀ e ∈ (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).map (fun idx => netE3 n + idx),
        e < netE4 n ∧ (rawEnds n e).2 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨idx, hidx, rfl⟩
      rcases List.mem_filter.mp hidx with ⟨hidx_r, hidx_p⟩
      have hidx_lt : idx < n := List.mem_range.mp hidx_r
      have hidx_eq : (idx / paramJ n) % paramL2 n = j2 := of_decide_eq_true hidx_p
      refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B3 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB3]; omega
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL1 n)).map
        (fun k => netE4 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)),
        netE4 n ≤ e ∧ e < netE5 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL1 n := List.mem_range.mp hk
      set off := (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE4 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE4 n + off := by dsimp [off]; omega
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        simpa [hL_mul] using affine_contig_lt hj2 hk_lt
      rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B4 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB4]
      have hdiv : (off / (2 * paramJ n)) / paramL1 n = j2 :=
        (dftIdx_div_iff h2J hL1 hj2 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    refine ⟨pairwise_lt_map (B := n) _ (pairwise_lt_filter _ (pairwise_lt_range n))
        (fun x hx => List.mem_range.mp (List.mem_filter.mp hx).1) (fun a b hab _ => by omega),
      pairwise_lt_map (B := 2 * paramJ n * paramL1 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := a)
          have h2 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := b)
          omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  by_cases hv5 : v < netV5 n
  · rw [(inOut_of_V4 (by omega) hv5).1, (inOut_of_V4 (by omega) hv5).2]
    have hV5 : netV5 n = netV4 n + paramL1 n := by simp [netV4, netV5]
    have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
    have hE6 : netE6 n = netE5 n + 2 * paramJ n * paramL n := rfl
    set q1 := v - netV4 n
    have hq1 : q1 < paramL1 n := by omega
    have hin_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE4 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)),
        e < netE5 n ∧ (rawEnds n e).2 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE4 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE4 n + off := by dsimp [off]; omega
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B4 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB4]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_left_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE5 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)),
        netE5 n ≤ e ∧ e < netE6 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE5 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE5 n + off := by dsimp [off]; omega
      have hoff_alt : off = ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) := by
        dsimp [off]; ring
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        rw [hoff_alt]; simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B5 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB5]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_right_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    refine ⟨pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 : (q1 + paramL1 n * (a / (2 * paramJ n))) = (a / (2 * paramJ n)) * paramL1 n + q1 := by ring
          have h2 : (q1 + paramL1 n * (b / (2 * paramJ n))) = (b / (2 * paramJ n)) * paramL1 n + q1 := by ring
          rw [h1, h2]; have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  rw [(inOut_of_V5 (by omega) hv6).1, (inOut_of_V5 (by omega) hv6).2]
  have hV6 : netV6 n = netV5 n + paramL2 n := by simp [netV5, netV6]; omega
  have hE1 : netE1 n = 2 * n := rfl; have hE2 : netE2 n = 4 * n := rfl
  have hE7 : netE7 n = netE6 n + 2 * paramJ n * paramL n := rfl
  set j2 := v - netV5 n
  have hj2 : j2 < paramL2 n := by omega
  have hin_spec : ∀ e ∈ (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).map (fun idx => netE1 n + n + idx),
      e < netE2 n ∧ (rawEnds n e).2 = v := by
    intro e he; rcases List.mem_map.mp he with ⟨idx, hidx, rfl⟩
    rcases List.mem_filter.mp hidx with ⟨hidx_r, hidx_p⟩
    have hidx_lt : idx < n := List.mem_range.mp hidx_r
    have hidx_eq : (idx / paramJ n) % paramL2 n = j2 := of_decide_eq_true hidx_p
    refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B1 (by omega) (by omega)]
    have hsub : netE1 n + n + idx - netE1 n = n + idx := by omega
    have hnlt : ¬(n + idx < n) := by omega
    have hsub2 : n + idx - n = idx := Nat.add_sub_cancel_left _ _
    rw [hsub]; dsimp [endsB1]; simp only [hnlt, ↓reduceIte, hsub2, hidx_eq]; omega
  have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL1 n)).map
      (fun k => netE6 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)),
      netE6 n ≤ e ∧ e < netE7 n ∧ (rawEnds n e).1 = v := by
    intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
    have hk_lt : k < 2 * paramJ n * paramL1 n := List.mem_range.mp hk
    set off := (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)
    have hoff_eq : netE6 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n) =
        netE6 n + off := by dsimp [off]; omega
    have hoff_lt : off < 2 * paramJ n * paramL n := by
      simpa [hL_mul] using affine_contig_lt hj2 hk_lt
    rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
    rw [rawEnds_of_B6 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB6]
    have hdiv : (off / (2 * paramJ n)) / paramL1 n = j2 :=
      (dftIdx_div_iff h2J hL1 hj2 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
    omega
  exact ⟨pairwise_lt_map (B := n) _ (pairwise_lt_filter _ (pairwise_lt_range n))
      (fun x hx => List.mem_range.mp (List.mem_filter.mp hx).1) (fun a b hab _ => by omega),
    pairwise_lt_map (B := 2 * paramJ n * paramL1 n) _ (pairwise_lt_range _)
      (fun x hx => List.mem_range.mp hx)
      (fun a b hab _ => by
        have h1 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := a)
        have h2 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := b)
        omega),
    fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
    fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
    fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩

lemma inOutEdges_spec_6_11 (n v : ℕ) (hv6 : netV6 n ≤ v) (hv12 : v < netV12 n) :
    InOutSpecProp n v := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hL_mul' : paramL n = paramL2 n * paramL1 n := by rw [hL_mul, Nat.mul_comm]
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, hv6_le, hv7_le, hv8_le, hv9_le, hv10_le, hv11_le, _⟩
  rcases netE_chain n with
    ⟨_, _, _, _, _, he5_le, he6_le, he7_le, he8_le, he9_le, he10_le, he11_le, he12_le, he13_lt⟩
  unfold InOutSpecProp
  by_cases hv7 : v < netV7 n
  · rw [(inOut_of_V6 hv6 hv7).1, (inOut_of_V6 hv6 hv7).2]
    have hV7 : netV7 n = netV6 n + paramL1 n := by simp [netV6, netV7]; omega
    have hE7 : netE7 n = netE6 n + 2 * paramJ n * paramL n := rfl
    have hE8 : netE8 n = netE7 n + 2 * paramJ n * paramL n := rfl
    set q1 := v - netV6 n
    have hq1 : q1 < paramL1 n := by omega
    have hin_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE6 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)),
        e < netE7 n ∧ (rawEnds n e).2 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE6 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE6 n + off := by dsimp [off]; omega
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B6 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB6]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_left_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE7 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)),
        netE7 n ≤ e ∧ e < netE8 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE7 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE7 n + off := by dsimp [off]; omega
      have hoff_alt : off = ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) := by
        dsimp [off]; ring
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        rw [hoff_alt]; simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B7 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB7]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_right_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    exact ⟨pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 : (q1 + paramL1 n * (a / (2 * paramJ n))) = (a / (2 * paramJ n)) * paramL1 n + q1 := by ring
          have h2 : (q1 + paramL1 n * (b / (2 * paramJ n))) = (b / (2 * paramJ n)) * paramL1 n + q1 := by ring
          rw [h1, h2]; have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  by_cases hv8 : v < netV8 n
  · rw [(inOut_of_V7 (by omega) hv8).1, (inOut_of_V7 (by omega) hv8).2]
    have hV8 : netV8 n = netV7 n + paramL n := rfl
    have hE6 : netE6 n = netE5 n + 2 * paramJ n * paramL n := rfl
    have hE8 : netE8 n = netE7 n + 2 * paramJ n * paramL n := rfl
    have hE9 : netE9 n = netE8 n + 2 * paramJ n * paramL n := rfl
    set q := v - netV7 n
    have hq : q < paramL n := by omega
    have hbound : ∀ p < 2 * paramJ n, q * (2 * paramJ n) + p < 2 * paramJ n * paramL n := by
      intro p hp
      have h1 : (q + 1) * (2 * paramJ n) ≤ paramL n * (2 * paramJ n) := Nat.mul_le_mul_right _ hq
      have h2 : (q + 1) * (2 * paramJ n) = q * (2 * paramJ n) + 2 * paramJ n := by ring
      have h3 : paramL n * (2 * paramJ n) = 2 * paramJ n * paramL n := by ring
      omega
    have hin_spec : ∀ e ∈
        (List.range (2 * paramJ n)).map (fun p => netE5 n + q * (2 * paramJ n) + p) ++
        (List.range (2 * paramJ n)).map (fun p => netE7 n + q * (2 * paramJ n) + p),
        e < netE8 n ∧ (rawEnds n e).2 = v := by
      intro e he; rw [List.mem_append] at he
      rcases he with he | he <;> {
        rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
        have hp_lt : p < 2 * paramJ n := List.mem_range.mp hp
        have hb := hbound p hp_lt
        obtain ⟨hd, _⟩ := mul_add_div_mod (q := q) h2J hp_lt
        first
        | (have heq : netE5 n + q * (2 * paramJ n) + p = netE5 n + (q * (2 * paramJ n) + p) := by omega
           rw [heq]; refine ⟨by omega, ?_⟩
           rw [rawEnds_of_B5 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB5]; rw [hd]; omega)
        | (have heq : netE7 n + q * (2 * paramJ n) + p = netE7 n + (q * (2 * paramJ n) + p) := by omega
           rw [heq]; refine ⟨by omega, ?_⟩
           rw [rawEnds_of_B7 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB7]; rw [hd]; omega)
      }
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n)).map (fun p => netE8 n + q * (2 * paramJ n) + p),
        netE8 n ≤ e ∧ e < netE9 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
      have hp_lt : p < 2 * paramJ n := List.mem_range.mp hp
      have hb := hbound p hp_lt
      have heq : netE8 n + q * (2 * paramJ n) + p = netE8 n + (q * (2 * paramJ n) + p) := by omega
      rw [heq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B8 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB8]
      obtain ⟨hd, _⟩ := mul_add_div_mod (q := q) h2J hp_lt; rw [hd]; omega
    exact ⟨pairwise_lt_append
        (pairwise_lt_map (B := 2 * paramJ n) _ (pairwise_lt_range _) (fun x hx => List.mem_range.mp hx) (fun a b hab _ => by omega))
        (pairwise_lt_map (B := 2 * paramJ n) _ (pairwise_lt_range _) (fun x hx => List.mem_range.mp hx) (fun a b hab _ => by omega))
        (fun x hx y hy => by
          rcases List.mem_map.mp hx with ⟨p1, hp1, rfl⟩
          rcases List.mem_map.mp hy with ⟨p2, _, rfl⟩
          have := hbound p1 (List.mem_range.mp hp1); omega),
      pairwise_lt_map (B := 2 * paramJ n) _ (pairwise_lt_range _) (fun x hx => List.mem_range.mp hx) (fun a b hab _ => by omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  by_cases hv9 : v < netV9 n
  · rw [(inOut_of_V8 (by omega) hv9).1, (inOut_of_V8 (by omega) hv9).2]
    have hV9 : netV9 n = netV8 n + paramL2 n := rfl
    have hE9 : netE9 n = netE8 n + 2 * paramJ n * paramL n := rfl
    have hE10 : netE10 n = netE9 n + 2 * paramJ n * paramL n := rfl
    set j2 := v - netV8 n
    have hj2 : j2 < paramL2 n := by omega
    have hin_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL1 n)).map
        (fun k => netE8 n + (paramL2 n * (k / (2 * paramJ n)) + j2) * (2 * paramJ n) + k % (2 * paramJ n)),
        e < netE9 n ∧ (rawEnds n e).2 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL1 n := List.mem_range.mp hk
      set off := (paramL2 n * (k / (2 * paramJ n)) + j2) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE8 n + (paramL2 n * (k / (2 * paramJ n)) + j2) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE8 n + off := by dsimp [off]; omega
      have hoff_alt : off = ((k / (2 * paramJ n)) * paramL2 n + j2) * (2 * paramJ n) + k % (2 * paramJ n) := by
        dsimp [off]; ring
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        rw [hoff_alt]; simpa [hL_mul'] using affine_stride_lt h2J hj2 hk_lt
      rw [hoff_eq]; refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B8 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB8]
      have hmod : (off / (2 * paramJ n)) % paramL2 n = j2 := by
        rw [hoff_alt]
        exact (dftIdx_mod_left_iff h2J hL2 hj2 (by rw [← hoff_alt]; simpa [hL_mul'] using hoff_lt)).mpr
          (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL1 n)).map
        (fun k => netE9 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)),
        netE9 n ≤ e ∧ e < netE10 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL1 n := List.mem_range.mp hk
      set off := (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE9 n + (j2 * paramL1 n + k / (2 * paramJ n)) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE9 n + off := by dsimp [off]; omega
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        simpa [hL_mul] using affine_contig_lt hj2 hk_lt
      rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B9 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB9]
      have hdiv : (off / (2 * paramJ n)) / paramL1 n = j2 :=
        (dftIdx_div_iff h2J hL1 hj2 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    exact ⟨pairwise_lt_map (B := 2 * paramJ n * paramL1 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 : paramL2 n * (a / (2 * paramJ n)) + j2 = (a / (2 * paramJ n)) * paramL2 n + j2 := by ring
          have h2 : paramL2 n * (b / (2 * paramJ n)) + j2 = (b / (2 * paramJ n)) * paramL2 n + j2 := by ring
          rw [h1, h2]; have := affine_stride_strictMono (b := j2) h2J hL2 hab; omega),
      pairwise_lt_map (B := 2 * paramJ n * paramL1 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := a)
          have h2 := affine_contig_eq (W := 2 * paramJ n) (c := j2 * paramL1 n) (k := b)
          omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  by_cases hv10 : v < netV10 n
  · rw [(inOut_of_V9 (by omega) hv10).1, (inOut_of_V9 (by omega) hv10).2]
    have hV10 : netV10 n = netV9 n + paramL1 n := rfl
    have hE10 : netE10 n = netE9 n + 2 * paramJ n * paramL n := rfl
    have hE11 : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
    set q1 := v - netV9 n
    have hq1 : q1 < paramL1 n := by omega
    have hin_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE9 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)),
        e < netE10 n ∧ (rawEnds n e).2 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE9 n + ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE9 n + off := by dsimp [off]; omega
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B9 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB9]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_left_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    have hout_spec : ∀ e ∈ (List.range (2 * paramJ n * paramL2 n)).map
        (fun k => netE10 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)),
        netE10 n ≤ e ∧ e < netE11 n ∧ (rawEnds n e).1 = v := by
      intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
      have hk_lt : k < 2 * paramJ n * paramL2 n := List.mem_range.mp hk
      set off := (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n)
      have hoff_eq : netE10 n + (q1 + paramL1 n * (k / (2 * paramJ n))) * (2 * paramJ n) + k % (2 * paramJ n) =
          netE10 n + off := by dsimp [off]; omega
      have hoff_alt : off = ((k / (2 * paramJ n)) * paramL1 n + q1) * (2 * paramJ n) + k % (2 * paramJ n) := by
        dsimp [off]; ring
      have hoff_lt : off < 2 * paramJ n * paramL n := by
        rw [hoff_alt]; simpa [hL_mul] using affine_stride_lt h2J hq1 hk_lt
      rw [hoff_eq]; refine ⟨by omega, by omega, ?_⟩
      rw [rawEnds_of_B10 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB10]
      have hmod : (off / (2 * paramJ n)) % paramL1 n = q1 :=
        (dftIdx_mod_right_iff h2J hL1 hq1 (by simpa [hL_mul] using hoff_lt)).mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
      omega
    exact ⟨pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      pairwise_lt_map (B := 2 * paramJ n * paramL2 n) _ (pairwise_lt_range _)
        (fun x hx => List.mem_range.mp hx)
        (fun a b hab _ => by
          have h1 : (q1 + paramL1 n * (a / (2 * paramJ n))) = (a / (2 * paramJ n)) * paramL1 n + q1 := by ring
          have h2 : (q1 + paramL1 n * (b / (2 * paramJ n))) = (b / (2 * paramJ n)) * paramL1 n + q1 := by ring
          rw [h1, h2]; have := affine_stride_strictMono (b := q1) h2J hL1 hab; omega),
      fun e1 he1 e2 he2 => by have := (hin_spec e1 he1).1; have := (hout_spec e2 he2).1; omega,
      fun e he => ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩,
      fun e he => ⟨by have := (hout_spec e he).2.1; omega, (hout_spec e he).2.2⟩⟩
  by_cases hv11 : v < netV11 n
  · rw [(inOut_of_V10 (by omega) hv11).1, (inOut_of_V10 (by omega) hv11).2]
    dsimp only
    have hV11 : netV11 n = netV10 n + 2 * paramJ n * paramL n := rfl
    have hE11 : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
    set k := v - netV10 n
    have hk : k < 2 * paramJ n * paramL n := by omega
    refine ⟨by split_ifs <;> simp, by simp, by simp, ?_, by simp⟩
    intro e he; split_ifs at he with htk
    · simp at he
    · simp only [List.mem_singleton] at he; subst he
      refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B10 (by omega) (by omega), Nat.add_sub_cancel_left]
      dsimp [endsB10]; simp only [htk, ↓reduceIte]; omega
  rw [(inOut_of_V11 (by omega) hv12).1, (inOut_of_V11 (by omega) hv12).2]
  have hV12 : netV12 n = netV11 n + 2 * n := rfl
  have hE11 : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
  have hE12 : netE12 n = netE11 n + 2 * n := rfl
  set tk := v - netV11 n
  have htk : tk < 2 * n := by omega
  obtain ⟨hpw, hbnd⟩ := ovlInLocal_spec (L := paramL n) (tk := tk) hJ
  have hin_spec : ∀ e ∈ (ovlInLocal (paramJ n) (paramL n) tk).map (fun k => netE10 n + k),
      e < netE11 n ∧ (rawEnds n e).2 = v := by
    intro e he; rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
    have hk_lt : k < 2 * paramJ n * paramL n := hbnd k hk
    have htk_eq : ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) = tk :=
      (ovlTargetBit_eq_iff hJ hk_lt).mpr hk
    refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B10 (by omega) (by omega), Nat.add_sub_cancel_left]
    dsimp [endsB10]; simp only [htk_eq, htk, ↓reduceIte]; omega
  refine ⟨pairwise_lt_map (B := 2 * paramJ n * paramL n) _ hpw hbnd (fun a b hab _ => by omega),
    by simp, ?_, ?_, ?_⟩
  · intro e1 he1 e2 he2; have := (hin_spec e1 he1).1; simp only [List.mem_singleton] at he2; subst he2; omega
  · intro e he; exact ⟨by have := (hin_spec e he).1; omega, (hin_spec e he).2⟩
  · intro e he; simp only [List.mem_singleton] at he; subst he
    refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B11 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB11]; omega

lemma inOutEdges_spec_12_15 (n v : ℕ) (hv12 : netV12 n ≤ v) (hv16 : v < netV16 n) :
    InOutSpecProp n v := by
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hv12_le, hv13_le, hv14_le, hv15_le, _⟩
  rcases netE_chain n with
    ⟨_, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  unfold InOutSpecProp
  by_cases hv13 : v < netV13 n
  · rw [(inOut_of_V12 hv12 hv13).1, (inOut_of_V12 hv12 hv13).2]
    have hV13 : netV13 n = netV12 n + n := rfl
    have hE1 : netE1 n = 2 * n := rfl; have hE2 : netE2 n = 4 * n := rfl
    have hE12 : netE12 n = netE11 n + 2 * n := rfl
    set i := v - netV12 n
    have hi : i < n := by omega
    refine ⟨pairwise_lt_three (by omega) (by omega), by simp, by simp, ?_, by simp⟩
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B1 (by omega) (by omega), Nat.add_sub_cancel_left]
      dsimp [endsB1]; simp only [hi, ↓reduceIte]; omega
    · refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B11 (by omega) (by omega), Nat.add_sub_cancel_left]
      dsimp [endsB11]; rw [Nat.mod_eq_of_lt hi]; omega
    · have heq : netE11 n + i + n = netE11 n + (i + n) := by omega
      rw [heq]; refine ⟨by omega, ?_⟩
      rw [rawEnds_of_B11 (by omega) (by omega), Nat.add_sub_cancel_left]
      dsimp [endsB11]; rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]; omega
  by_cases hv14 : v < netV14 n
  · rw [(inOut_of_V13 (by omega) hv14).1, (inOut_of_V13 (by omega) hv14).2]
    have hV14 : netV14 n = netV13 n + (treeM n - n) := rfl
    have hE2 : netE2 n = 4 * n := rfl; have hE3 : netE3 n = 4 * n + 2 * treeM n := rfl
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    have heq : netE2 n + n + (v - netV13 n) = netE2 n + (n + (v - netV13 n)) := by omega
    rw [heq]; refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B2 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB2]; split_ifs <;> omega
  by_cases hv15 : v < netV15 n
  · rw [(inOut_of_V14 (by omega) hv15).1, (inOut_of_V14 (by omega) hv15).2]
    have hV15 : netV15 n = netV14 n + (treeM n - n) := rfl
    have hE2 : netE2 n = 4 * n := rfl; have hE3 : netE3 n = 4 * n + 2 * treeM n := rfl
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    have heq : netE2 n + treeM n + n + (v - netV14 n) = netE2 n + (treeM n + n + (v - netV14 n)) := by omega
    rw [heq]; refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B2 (by omega) (by omega), Nat.add_sub_cancel_left]; dsimp [endsB2]; split_ifs <;> omega
  set r := treeLog n + 1
  have hV16 : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
  have hE2 : netE2 n = 4 * n := rfl; have hE3 : netE3 n = 4 * n + 2 * treeM n := rfl
  have hE13 : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl
  set locV := v - netV15 n
  have hlocV : locV < treeVertOff r (r + 1) := by omega
  obtain ⟨hj1, hjr, hnode, hu, hlocV_eq⟩ := decodeTreeVert_spec hlocV
  set tv := decodeTreeVert r locV
  set j := tv.1; set node := tv.2.1; set u := tv.2.2
  have htv : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (j, node, u) := by
    rcases htv_eq : tv with ⟨_, _, _⟩; rfl
  rw [inEdges_of_V15 (by omega) hv16 htv, outEdges_of_V15 (by omega) hv16 htv]
  dsimp only
  by_cases hu0 : u = 0
  · simp only [hu0, ↓reduceIte]
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    have hlocE : treeEdgeOff r j + node * (2 * j + 1) + 0 < treeEdgeOff r (r + 1) :=
      encodeTreeEdge_lt hj1 hjr hnode (by omega)
    have he_eq : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) =
        netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 0) := by dsimp [r]; omega
    rw [he_eq]; refine ⟨by omega, ?_⟩
    rw [rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
        endsB12_of_decode (decodeTreeEdge_encode hj1 hjr hnode (by omega))]
    dsimp only; simp only [↓reduceIte]
    change netV15 n + treeVertOff r j + node * (j + 1) = v; omega
  · simp only [hu0, ↓reduceIte]
    set b := u - 1
    have hb_lt : b < j := by omega
    set base := netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1)
    have hcin_lt : treeEdgeOff r j + node * (2 * j + 1) + 2 * b < treeEdgeOff r (r + 1) :=
      encodeTreeEdge_lt hj1 hjr hnode (by omega)
    have hcin_end : (rawEnds n (base + 2 * b)).2 = v := by
      have he_eq : base + 2 * b = netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * b) := by
        dsimp [base, r]; omega
      rw [he_eq, rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
          endsB12_of_decode (decodeTreeEdge_encode hj1 hjr hnode (by omega))]
      dsimp only
      have hcond : (2 * b) % 2 = 0 ∧ 2 * b < 2 * j := ⟨by omega, by omega⟩
      simp only [hcond, and_self, ↓reduceIte]
      have hdiv : (2 * b) / 2 = b := by omega
      rw [hdiv]; change netV15 n + treeVertOff r j + node * (j + 1) + 1 + b = v; omega
    have hout_spec : ∀ e ∈ [base + 2 * b + 1, base + 2 * b + 2],
        base + 2 * b < e ∧ e < netEdgeCount n ∧ (rawEnds n e).1 = v := by
      intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have hw_lt : 2 * b + 1 < 2 * j + 1 := by omega
        have hlocE := encodeTreeEdge_lt hj1 hjr hnode hw_lt
        have he_eq : base + 2 * b + 1 =
            netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + (2 * b + 1)) := by dsimp [base, r]; omega
        refine ⟨by omega, by omega, ?_⟩
        rw [he_eq, rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
            endsB12_of_decode (decodeTreeEdge_encode hj1 hjr hnode hw_lt)]
        dsimp only; simp only [show ¬(2 * b + 1 = 0) by omega, ↓reduceIte]
        have hdiv : (2 * b + 1 - 1) / 2 = b := by omega
        rw [hdiv]; change netV15 n + treeVertOff r j + node * (j + 1) + 1 + b = v; omega
      · have hw_lt : 2 * b + 2 < 2 * j + 1 := by omega
        have hlocE := encodeTreeEdge_lt hj1 hjr hnode hw_lt
        have he_eq : base + 2 * b + 2 =
            netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + (2 * b + 2)) := by dsimp [base, r]; omega
        refine ⟨by omega, by omega, ?_⟩
        rw [he_eq, rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
            endsB12_of_decode (decodeTreeEdge_encode hj1 hjr hnode hw_lt)]
        dsimp only; simp only [show ¬(2 * b + 2 = 0) by omega, ↓reduceIte]
        have hdiv : (2 * b + 2 - 1) / 2 = b := by omega
        rw [hdiv]; change netV15 n + treeVertOff r j + node * (j + 1) + 1 + b = v; omega
    by_cases hj_eq1 : j = 1
    · simp only [hj_eq1, ↓reduceIte]
      have hb0 : b = 0 := by omega
      have hnode_M1 : node < treeM n := by
        have hr1 : r - 1 = treeLog n := rfl
        simpa [hj_eq1, hr1, treeM] using hnode
      have hv_eq : v = netV15 n + node * 2 + 1 := by
        have ht0 : treeVertOff r 1 = 0 := rfl
        have hu1 : u = 1 := by omega
        change locV = treeVertOff r j + node * (j + 1) + u at hlocV_eq
        rw [hj_eq1, ht0, hu1] at hlocV_eq; omega
      have hin_j1 : ∀ e ∈ [netE2 n + 2 * node, netE2 n + 2 * node + 1, base + 2 * b],
          e ≤ base + 2 * b ∧ e < netEdgeCount n ∧ (rawEnds n e).2 = v := by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · refine ⟨by dsimp [base]; omega, by omega, ?_⟩
          rw [rawEnds_of_B2 (by omega) (by omega), Nat.add_sub_cancel_left]
          dsimp [endsB2]
          have hd : (2 * node) / 2 = node := by omega
          rw [hd, hv_eq]
        · have heq : netE2 n + 2 * node + 1 = netE2 n + (2 * node + 1) := by omega
          refine ⟨by dsimp [base]; omega, by omega, ?_⟩
          rw [heq, rawEnds_of_B2 (by omega) (by omega), Nat.add_sub_cancel_left]
          dsimp [endsB2]
          have hd : (2 * node + 1) / 2 = node := by omega
          rw [hd, hv_eq]
        · exact ⟨le_rfl, by dsimp [base, r] at *; omega, hcin_end⟩
      exact ⟨pairwise_lt_three (by omega) (by dsimp [base]; omega),
        pairwise_lt_two (by omega),
        fun e1 he1 e2 he2 => by have := (hin_j1 e1 he1).1; have := (hout_spec e2 he2).1; omega,
        fun e he => (hin_j1 e he).2,
        fun e he => (hout_spec e he).2⟩
    · simp only [hj_eq1, ↓reduceIte]
      set j' := j - 1
      have hj'1 : 1 ≤ j' := by omega
      have hj'r : j' < r := by omega
      have hb_le : b ≤ j' := by omega
      set sw := sumWireLoc j' b
      have hsw_lt : sw < 2 * j' + 1 := sumWireLoc_lt hb_le
      obtain ⟨hsw_not, hsw_bit⟩ := (sumWireLoc_iff hj'1 hsw_lt hb_le).mpr rfl
      have hpow_c : 2 ^ (r - j') = 2 * 2 ^ (r - j) := by
        have hexp : r - j' = (r - j) + 1 := by omega
        rw [hexp, pow_succ']
      have hc0 : 2 * node < 2 ^ (r - j') := by omega
      have hc1 : 2 * node + 1 < 2 ^ (r - j') := by omega
      have hstep_off : treeEdgeOff r j = treeEdgeOff r j' + (2 * j' + 1) * 2 ^ (r - j') := by
        rcases Nat.exists_eq_succ_of_ne_zero (show j' ≠ 0 by omega) with ⟨m, hm⟩
        have hj_succ : j = m + 2 := by omega
        rw [hj_succ, hm]; rfl
      have hc1_lt_j : treeEdgeOff r j' + (2 * node + 1) * (2 * j' + 1) + sw < treeEdgeOff r j := by
        have hm1 : (2 * node + 2) * (2 * j' + 1) ≤ 2 ^ (r - j') * (2 * j' + 1) := Nat.mul_le_mul_right _ hc1
        have hm2 : (2 * node + 2) * (2 * j' + 1) = (2 * node + 1) * (2 * j' + 1) + (2 * j' + 1) := by ring
        have hm3 : 2 ^ (r - j') * (2 * j' + 1) = (2 * j' + 1) * 2 ^ (r - j') := Nat.mul_comm _ _
        omega
      have hc0_lt_c1 : treeEdgeOff r j' + (2 * node) * (2 * j' + 1) + sw <
          treeEdgeOff r j' + (2 * node + 1) * (2 * j' + 1) + sw := by
        have : (2 * node + 1) * (2 * j' + 1) = (2 * node) * (2 * j' + 1) + (2 * j' + 1) := by ring
        omega
      have hchild_end : ∀ cnode, cnode < 2 ^ (r - j') → cnode / 2 = node →
          (rawEnds n (netE12 n + treeEdgeOff (treeLog n + 1) j' + cnode * (2 * j' + 1) + sw)).2 = v := by
        intro cnode hcnode hcdiv
        have hloc_c := encodeTreeEdge_lt hj'1 (le_of_lt hj'r) hcnode hsw_lt
        have he_eq : netE12 n + treeEdgeOff (treeLog n + 1) j' + cnode * (2 * j' + 1) + sw =
            netE12 n + (treeEdgeOff r j' + cnode * (2 * j' + 1) + sw) := by dsimp [r]; omega
        rw [he_eq, rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
            endsB12_of_decode (decodeTreeEdge_encode hj'1 (le_of_lt hj'r) hcnode hsw_lt)]
        dsimp only
        have hj'r_raw : j' < treeLog n + 1 := hj'r
        simp only [hsw_not, ↓reduceIte, hsw_bit, hj'r_raw, hcdiv]
        have hj_succ : j' + 1 = j := by omega
        have hj_succ2 : j' + 2 = j + 1 := by omega
        rw [hj_succ, hj_succ2]
        change netV15 n + treeVertOff r j + node * (j + 1) + 1 + b = v; omega
      set eL := netE12 n + treeEdgeOff (treeLog n + 1) j' + (2 * node) * (2 * j' + 1) + sw
      set eR := netE12 n + treeEdgeOff (treeLog n + 1) j' + (2 * node + 1) * (2 * j' + 1) + sw
      have hin_gt1 : ∀ e ∈ [eL, eR, base + 2 * b],
          e ≤ base + 2 * b ∧ e < netEdgeCount n ∧ (rawEnds n e).2 = v := by
        intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨by dsimp [eL, base, r] at *; omega, by dsimp [eL, base, r] at *; omega,
            hchild_end (2 * node) hc0 (by omega)⟩
        · exact ⟨by dsimp [eR, base, r] at *; omega, by dsimp [eR, base, r] at *; omega,
            hchild_end (2 * node + 1) hc1 (by omega)⟩
        · exact ⟨le_rfl, by dsimp [base, r] at *; omega, hcin_end⟩
      exact ⟨pairwise_lt_three (by dsimp [eL, eR, r] at *; omega) (by dsimp [eR, base, r] at *; omega),
        pairwise_lt_two (by omega),
        fun e1 he1 e2 he2 => by have := (hin_gt1 e1 he1).1; have := (hout_spec e2 he2).1; omega,
        fun e he => (hin_gt1 e he).2,
        fun e he => (hout_spec e he).2⟩

lemma inOutEdges_spec_16_18 (n v : ℕ) (hv16 : netV16 n ≤ v) (hv : v < netVertCount n) :
    InOutSpecProp n v := by
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, he12_le, he13_lt⟩
  unfold InOutSpecProp
  by_cases hv17 : v < netV17 n
  · rw [(inOut_of_V16 hv16 hv17).1, (inOut_of_V16 hv16 hv17).2]
    have hV17 : netV17 n = netV16 n + 1 := rfl
    refine ⟨by simp, by simp, by simp, by simp, ?_⟩
    intro e he; simp only [List.mem_singleton] at he; subst he
    refine ⟨by omega, ?_⟩; rw [rawEnds_of_B13 (by omega), Nat.sub_self]; dsimp [endsB13]; omega
  by_cases hv18 : v < netV18 n
  · rw [(inOut_of_V17 (by omega) hv18).1, (inOut_of_V17 (by omega) hv18).2]
    set r := treeLog n + 1
    have hV18 : netV18 n = netV17 n + (r + 1) := rfl
    have hE13 : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl
    have hE14 : netEdgeCount n = netE13 n + (r + 2) := rfl
    set b := v - netV17 n
    have hb_lt : b < r + 1 := by omega
    have hb_le : b ≤ r := by omega
    set sw := sumWireLoc r b
    have hsw_lt : sw < 2 * r + 1 := sumWireLoc_lt hb_le
    obtain ⟨hsw_not, hsw_bit⟩ := (sumWireLoc_iff (by dsimp [r]; omega) hsw_lt hb_le).mpr rfl
    have hlocE : treeEdgeOff r r + 0 * (2 * r + 1) + sw < treeEdgeOff r (r + 1) :=
      encodeTreeEdge_lt (by dsimp [r]; omega) le_rfl (by simp) hsw_lt
    have hin_cmp : ∀ e ∈ [netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 1) + sw, netE13 n + b],
        e ≤ netE13 n + b ∧ e < netEdgeCount n ∧ (rawEnds n e).2 = v := by
      intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have he_eq : netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 1) + sw =
            netE12 n + (treeEdgeOff r r + 0 * (2 * r + 1) + sw) := by dsimp [r]; omega
        have hdec_top : decodeTreeEdge (treeLog n + 1) (treeEdgeOff r r + 0 * (2 * r + 1) + sw) = (r, 0, sw) :=
          decodeTreeEdge_encode (r := r) (by dsimp [r]; omega) le_rfl (by simp) hsw_lt
        refine ⟨by dsimp [r] at *; omega, by dsimp [r] at *; omega, ?_⟩
        rw [he_eq, rawEnds_of_B12 (by omega) (by omega), Nat.add_sub_cancel_left,
            endsB12_of_decode hdec_top]
        dsimp only
        have hnr : ¬(r < treeLog n + 1) := by dsimp [r]; omega
        simp only [hsw_not, ↓reduceIte, hsw_bit, hnr]; omega
      · refine ⟨le_rfl, by omega, ?_⟩
        rw [rawEnds_of_B13 (by omega), Nat.add_sub_cancel_left]; dsimp [endsB13]
        change (if b < r + 1 then netV17 n + b else netV18 n) = v
        simp only [hb_lt, ↓reduceIte]; omega
    exact ⟨pairwise_lt_two (by dsimp [r] at *; omega), by simp,
      fun e1 he1 e2 he2 => by
        have := (hin_cmp e1 he1).1; simp only [List.mem_singleton] at he2; subst he2; omega,
      fun e he => (hin_cmp e he).2,
      fun e he => by
        simp only [List.mem_singleton] at he; subst he
        have he_eq : netE13 n + b + 1 = netE13 n + (b + 1) := by omega
        refine ⟨by omega, ?_⟩
        rw [he_eq, rawEnds_of_B13 (by omega), Nat.add_sub_cancel_left]; dsimp [endsB13]; omega⟩
  rw [(inOut_of_V18 (by omega)).1, (inOut_of_V18 (by omega)).2]
  have hV19 : netVertCount n = netV18 n + 1 := rfl
  have hv_eq : v = netV18 n := by omega
  have hE14 : netEdgeCount n = netE13 n + (treeLog n + 3) := rfl
  refine ⟨by simp, by simp, by simp, ?_, by simp⟩
  intro e he; simp only [List.mem_singleton] at he; subst he
  refine ⟨by omega, ?_⟩
  rw [rawEnds_of_B13 (by omega), Nat.add_sub_cancel_left]; dsimp [endsB13]
  simp only [Nat.lt_irrefl (treeLog n + 2), ↓reduceIte, hv_eq]

lemma inOutEdges_spec (n v : ℕ) (hv : v < netVertCount n) :
    (inEdges n v).Pairwise (· < ·) ∧
    (outEdges n v).Pairwise (· < ·) ∧
    (∀ e1 ∈ inEdges n v, ∀ e2 ∈ outEdges n v, e1 < e2) ∧
    (∀ e ∈ inEdges n v, e < netEdgeCount n ∧ (rawEnds n e).2 = v) ∧
    (∀ e ∈ outEdges n v, e < netEdgeCount n ∧ (rawEnds n e).1 = v) := by
  change InOutSpecProp n v
  by_cases hv6 : v < netV6 n
  · exact inOutEdges_spec_0_5 n v hv6
  by_cases hv12 : v < netV12 n
  · exact inOutEdges_spec_6_11 n v (by omega) hv12
  by_cases hv16 : v < netV16 n
  · exact inOutEdges_spec_12_15 n v (by omega) hv16
  · exact inOutEdges_spec_16_18 n v (by omega) hv

lemma rawEnds_mem_0_7 (n e : ℕ) (he8 : e < netE8 n) :
    e ∈ outEdges n (rawEnds n e).1 ∧ e ∈ inEdges n (rawEnds n e).2 := by
  have h2J : 0 < 2 * paramJ n := by have := paramJ_pos n; omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netV_chain n with
    ⟨hv0, hv1_le, hv2_le, hv3_le, hv4_le, hv5_le, hv6_le, hv7_le, hv8_le, hv9_le,
     hv10_le, hv11_le, hv12_le, hv13_le, hv14_le, hv15_le, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with ⟨he0_le, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, _⟩
  by_cases he1 : e < netE1 n
  · rw [rawEnds_of_B0 he1]; dsimp [endsB0, netV0]
    have hE1 : netE1 n = 2 * n := rfl; have hV1 : netV1 n = 2 * n := rfl; have hV2 : netV2 n = 4 * n := rfl
    rw [(inOut_of_V0 (by omega)).2, (inOut_of_V1 (by omega) (by omega)).1]
    simp [netE0]
  by_cases he2 : e < netE2 n
  · rw [rawEnds_of_B1 (by omega) he2]
    have hE1 : netE1 n = 2 * n := rfl; have hE2 : netE2 n = 4 * n := rfl
    have hV1 : netV1 n = 2 * n := rfl; have hV2 : netV2 n = 4 * n := rfl
    have hV6 : netV6 n = netV5 n + paramL2 n := by simp [netV5, netV6]; omega
    have hV13 : netV13 n = netV12 n + n := rfl
    dsimp [endsB1]
    set i := e - netE1 n
    have hi : i < 2 * n := by omega
    constructor
    · rw [(inOut_of_V1 (by omega) (by omega)).2, Nat.add_sub_cancel_left]
      simp [show e = netE1 n + i by omega]
    · by_cases hin : i < n
      · simp only [hin, ↓reduceIte]
        rw [(inOut_of_V12 (by omega) (by omega)).1, Nat.add_sub_cancel_left]
        simp [show e = netE1 n + i by omega]
      · simp only [hin, ↓reduceIte]
        set idx := i - n
        have hidx : idx < n := by omega
        have hj2 : (idx / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
        rw [(inOut_of_V5 (by omega) (by omega)).1, Nat.add_sub_cancel_left, List.mem_map]
        exact ⟨idx, List.mem_filter.mpr ⟨List.mem_range.mpr hidx, decide_eq_true rfl⟩, by omega⟩
  by_cases he3 : e < netE3 n
  · rw [rawEnds_of_B2 (by omega) he3]
    have hE2 : netE2 n = 4 * n := rfl; have hE3 : netE3 n = 4 * n + 2 * treeM n := rfl
    have hV1 : netV1 n = 2 * n := rfl; have hV2 : netV2 n = 4 * n := rfl
    have hV14 : netV14 n = netV13 n + (treeM n - n) := rfl
    have hV15 : netV15 n = netV14 n + (treeM n - n) := rfl
    set r := treeLog n + 1
    have hV16 : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
    dsimp [endsB2]
    set leaf := e - netE2 n
    have hleaf : leaf < 2 * treeM n := by omega
    constructor
    · by_cases hl1 : leaf < n
      · simp only [hl1, ↓reduceIte]
        rw [(inOut_of_V1 (by omega) (by omega)).2, Nat.add_sub_cancel_left]
        simp [hl1, show e = netE2 n + leaf by omega]
      · simp only [hl1, ↓reduceIte]
        by_cases hl2 : leaf < treeM n
        · simp only [hl2, ↓reduceIte]
          rw [(inOut_of_V13 (by omega) (by omega)).2, Nat.add_sub_cancel_left, List.mem_singleton]; omega
        · simp only [hl2, ↓reduceIte]
          by_cases hl3 : leaf < treeM n + n
          · simp only [hl3, ↓reduceIte]
            have heq_v : netV1 n + n + (leaf - treeM n) = netV1 n + (n + (leaf - treeM n)) := by omega
            rw [heq_v, (inOut_of_V1 (by omega) (by omega)).2, Nat.add_sub_cancel_left]
            simp only [show ¬(n + (leaf - treeM n) < n) by omega, ↓reduceIte,
                       List.mem_cons, List.not_mem_nil, or_false]
            right; omega
          · simp only [hl3, ↓reduceIte]
            rw [(inOut_of_V14 (by omega) (by omega)).2, Nat.add_sub_cancel_left, List.mem_singleton]; omega
    · set node := leaf / 2
      have hnode : node < 2 ^ (r - 1) := by
        dsimp [node, r]; simpa [treeM] using Nat.div_lt_of_lt_mul hleaf
      have hlocV_lt : node * 2 + 1 < treeVertOff r (r + 1) := by
        simpa [treeVertOff] using encodeTreeVert_lt (r := r) (j := 1) (node := node) (u := 1)
          le_rfl (by dsimp [r]; omega) hnode (by omega)
      set dst := netV15 n + (node * 2 + 1)
      have hdst_eq : netV15 n + node * 2 + 1 = dst := by dsimp [dst]; omega
      have hdec : decodeTreeVert r (dst - netV15 n) = (1, node, 1) := by
        have ht0 : treeVertOff r 1 = 0 := rfl
        have hsub : dst - netV15 n = treeVertOff r 1 + node * (1 + 1) + 1 := by
          dsimp [dst]; rw [Nat.add_sub_cancel_left, ht0]; omega
        rw [hsub]; exact decodeTreeVert_encode le_rfl (by dsimp [r]; omega) hnode (by omega)
      rw [hdst_eq, inEdges_of_V15 (Nat.le_add_right _ _) (by rw [hV16]; exact Nat.add_lt_add_left hlocV_lt _) hdec]
      dsimp only
      simp only [show ¬(1 = 0) by decide, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      have hdm : 2 * node + leaf % 2 = leaf := Nat.div_add_mod leaf 2
      omega
  by_cases he4 : e < netE4 n
  · rw [rawEnds_of_B3 (by omega) he4]
    have hE4 : netE4 n = netE3 n + n := rfl
    have hV2 : netV2 n = 4 * n := rfl; have hV3 : netV3 n = 5 * n := rfl
    have hV4 : netV4 n = netV3 n + paramL2 n := by simp [netV3, netV4]
    dsimp [endsB3]
    set idx := e - netE3 n
    have hidx : idx < n := by omega
    have hj2 : (idx / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
    constructor
    · rw [(inOut_of_V2 (by omega) (by omega)).2, Nat.add_sub_cancel_left, List.mem_singleton]; omega
    · rw [(inOut_of_V3 (Nat.le_add_right _ _) (by rw [hV4]; exact Nat.add_lt_add_left hj2 _)).1,
          Nat.add_sub_cancel_left, List.mem_map]
      exact ⟨idx, List.mem_filter.mpr ⟨List.mem_range.mpr hidx, decide_eq_true rfl⟩, by omega⟩
  by_cases he5 : e < netE5 n
  · rw [rawEnds_of_B4 (by omega) he5]
    have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
    have hV4 : netV4 n = netV3 n + paramL2 n := by simp [netV3, netV4]
    have hV5 : netV5 n = netV4 n + paramL1 n := by simp [netV4, netV5]
    dsimp [endsB4]
    set idx := e - netE4 n
    have hidx : idx < 2 * paramJ n * (paramL1 n * paramL2 n) := by rw [← hL_mul]; omega
    have hj2 : (idx / (2 * paramJ n)) / paramL1 n < paramL2 n := by
      have hk : idx < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
        calc idx < 2 * paramJ n * (paramL1 n * paramL2 n) := hidx
             _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by ring
      have hrem : idx / (2 * paramJ n) < paramL2 n * paramL1 n :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : (idx / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    constructor
    · rw [(inOut_of_V3 (Nat.le_add_right _ _) (by rw [hV4]; exact Nat.add_lt_add_left hj2 _)).2,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_div_iff h2J hL1 hj2 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
    · rw [(inOut_of_V4 (Nat.le_add_right _ _) (by rw [hV5]; exact Nat.add_lt_add_left hq1 _)).1,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_left_iff h2J hL1 hq1 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
  by_cases he6 : e < netE6 n
  · rw [rawEnds_of_B5 (by omega) he6]
    have hE6 : netE6 n = netE5 n + 2 * paramJ n * paramL n := rfl
    have hV5 : netV5 n = netV4 n + paramL1 n := by simp [netV4, netV5]
    have hV8 : netV8 n = netV7 n + paramL n := rfl
    dsimp [endsB5]
    set idx := e - netE5 n
    have hidx_L : idx < 2 * paramJ n * paramL n := by omega
    have hidx : idx < 2 * paramJ n * (paramL1 n * paramL2 n) := by rwa [← hL_mul]
    set q := idx / (2 * paramJ n)
    have hq : q < paramL n := Nat.div_lt_of_lt_mul hidx_L
    have hq1 : q % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    constructor
    · rw [(inOut_of_V4 (Nat.le_add_right _ _) (by rw [hV5]; exact Nat.add_lt_add_left hq1 _)).2,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_right_iff h2J hL1 hq1 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
    · rw [(inOut_of_V7 (Nat.le_add_right _ _) (by rw [hV8]; exact Nat.add_lt_add_left hq _)).1,
          Nat.add_sub_cancel_left, List.mem_append]
      left
      refine List.mem_map.mpr ⟨idx % (2 * paramJ n), List.mem_range.mpr (Nat.mod_lt _ h2J), ?_⟩
      have hdm : 2 * paramJ n * q + idx % (2 * paramJ n) = idx := Nat.div_add_mod idx (2 * paramJ n)
      rw [Nat.mul_comm] at hdm; omega
  by_cases he7 : e < netE7 n
  · rw [rawEnds_of_B6 (by omega) he7]
    have hE7 : netE7 n = netE6 n + 2 * paramJ n * paramL n := rfl
    have hV6 : netV6 n = netV5 n + paramL2 n := by simp [netV5, netV6]; omega
    have hV7 : netV7 n = netV6 n + paramL1 n := by simp [netV6, netV7]; omega
    dsimp [endsB6]
    set idx := e - netE6 n
    have hidx : idx < 2 * paramJ n * (paramL1 n * paramL2 n) := by rw [← hL_mul]; omega
    have hj2 : (idx / (2 * paramJ n)) / paramL1 n < paramL2 n := by
      have hk : idx < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
        calc idx < 2 * paramJ n * (paramL1 n * paramL2 n) := hidx
             _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by ring
      have hrem : idx / (2 * paramJ n) < paramL2 n * paramL1 n :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : (idx / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    constructor
    · rw [(inOut_of_V5 (Nat.le_add_right _ _) (by rw [hV6]; exact Nat.add_lt_add_left hj2 _)).2,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_div_iff h2J hL1 hj2 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
    · rw [(inOut_of_V6 (Nat.le_add_right _ _) (by rw [hV7]; exact Nat.add_lt_add_left hq1 _)).1,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_left_iff h2J hL1 hq1 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
  rw [rawEnds_of_B7 (by omega) he8]
  have hE8 : netE8 n = netE7 n + 2 * paramJ n * paramL n := rfl
  have hV7 : netV7 n = netV6 n + paramL1 n := by simp [netV6, netV7]; omega
  have hV8 : netV8 n = netV7 n + paramL n := rfl
  dsimp [endsB7]
  set idx := e - netE7 n
  have hidx_L : idx < 2 * paramJ n * paramL n := by omega
  have hidx : idx < 2 * paramJ n * (paramL1 n * paramL2 n) := by rwa [← hL_mul]
  set q := idx / (2 * paramJ n)
  have hq : q < paramL n := Nat.div_lt_of_lt_mul hidx_L
  have hq1 : q % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
  constructor
  · rw [(inOut_of_V6 (Nat.le_add_right _ _) (by rw [hV7]; exact Nat.add_lt_add_left hq1 _)).2,
        Nat.add_sub_cancel_left]
    rcases List.mem_map.mp ((dftIdx_mod_right_iff h2J hL1 hq1 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
    exact List.mem_map.mpr ⟨k, hk, by omega⟩
  · rw [(inOut_of_V7 (Nat.le_add_right _ _) (by rw [hV8]; exact Nat.add_lt_add_left hq _)).1,
        Nat.add_sub_cancel_left, List.mem_append]
    right
    refine List.mem_map.mpr ⟨idx % (2 * paramJ n), List.mem_range.mpr (Nat.mod_lt _ h2J), ?_⟩
    have hdm : 2 * paramJ n * q + idx % (2 * paramJ n) = idx := Nat.div_add_mod idx (2 * paramJ n)
    rw [Nat.mul_comm] at hdm; omega

lemma rawEnds_mem_8_13 (n e : ℕ) (he8 : netE8 n ≤ e) (he : e < netEdgeCount n) :
    e ∈ outEdges n (rawEnds n e).1 ∧ e ∈ inEdges n (rawEnds n e).2 := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hL_mul' : paramL n = paramL2 n * paramL1 n := by rw [hL_mul, Nat.mul_comm]
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, hv7_le, hv8_le, hv9_le,
     hv10_le, hv11_le, hv12_le, hv13_le, hv14_le, hv15_le, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with
    ⟨_, _, _, _, _, _, _, _, he8_le, he9_le, he10_le, he11_le, he12_le, he13_lt⟩
  by_cases he9 : e < netE9 n
  · rw [rawEnds_of_B8 he8 he9]
    have hE9 : netE9 n = netE8 n + 2 * paramJ n * paramL n := rfl
    have hV8 : netV8 n = netV7 n + paramL n := rfl
    have hV9 : netV9 n = netV8 n + paramL2 n := rfl
    dsimp [endsB8]
    set idx := e - netE8 n
    have hidx_L : idx < 2 * paramJ n * paramL n := by omega
    have hidx : idx < 2 * paramJ n * (paramL2 n * paramL1 n) := by rwa [← hL_mul']
    set q := idx / (2 * paramJ n)
    have hq : q < paramL n := Nat.div_lt_of_lt_mul hidx_L
    have hj2 : q % paramL2 n < paramL2 n := Nat.mod_lt _ hL2
    constructor
    · rw [(inOut_of_V7 (Nat.le_add_right _ _) (by rw [hV8]; exact Nat.add_lt_add_left hq _)).2,
          Nat.add_sub_cancel_left]
      refine List.mem_map.mpr ⟨idx % (2 * paramJ n), List.mem_range.mpr (Nat.mod_lt _ h2J), ?_⟩
      have hdm : 2 * paramJ n * q + idx % (2 * paramJ n) = idx := Nat.div_add_mod idx (2 * paramJ n)
      rw [Nat.mul_comm] at hdm; omega
    · rw [(inOut_of_V8 (Nat.le_add_right _ _) (by rw [hV9]; exact Nat.add_lt_add_left hj2 _)).1,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_left_iff h2J hL2 hj2 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      refine List.mem_map.mpr ⟨k, hk, ?_⟩
      have hmul_c : paramL2 n * (k / (2 * paramJ n)) = (k / (2 * paramJ n)) * paramL2 n := Nat.mul_comm _ _
      rw [hmul_c]; omega
  by_cases he10 : e < netE10 n
  · rw [rawEnds_of_B9 (by omega) he10]
    have hE10 : netE10 n = netE9 n + 2 * paramJ n * paramL n := rfl
    have hV9 : netV9 n = netV8 n + paramL2 n := rfl
    have hV10 : netV10 n = netV9 n + paramL1 n := rfl
    dsimp [endsB9]
    set idx := e - netE9 n
    have hidx : idx < 2 * paramJ n * (paramL1 n * paramL2 n) := by rw [← hL_mul]; omega
    have hj2 : (idx / (2 * paramJ n)) / paramL1 n < paramL2 n := by
      have hk : idx < (paramL2 n * paramL1 n) * (2 * paramJ n) := by
        calc idx < 2 * paramJ n * (paramL1 n * paramL2 n) := hidx
             _ = (paramL2 n * paramL1 n) * (2 * paramJ n) := by ring
      have hrem : idx / (2 * paramJ n) < paramL2 n * paramL1 n :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    have hq1 : (idx / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    constructor
    · rw [(inOut_of_V8 (Nat.le_add_right _ _) (by rw [hV9]; exact Nat.add_lt_add_left hj2 _)).2,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_div_iff h2J hL1 hj2 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
    · rw [(inOut_of_V9 (Nat.le_add_right _ _) (by rw [hV10]; exact Nat.add_lt_add_left hq1 _)).1,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_left_iff h2J hL1 hq1 hidx).mp rfl) with ⟨k, hk, hk_eq⟩
      exact List.mem_map.mpr ⟨k, hk, by omega⟩
  by_cases he11 : e < netE11 n
  · rw [rawEnds_of_B10 (by omega) he11]
    have hE11 : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
    have hV10 : netV10 n = netV9 n + paramL1 n := rfl
    have hV11 : netV11 n = netV10 n + 2 * paramJ n * paramL n := rfl
    have hV12 : netV12 n = netV11 n + 2 * n := rfl
    dsimp [endsB10]
    set k := e - netE10 n
    have hk_L : k < 2 * paramJ n * paramL n := by omega
    have hk : k < 2 * paramJ n * (paramL1 n * paramL2 n) := by rwa [← hL_mul]
    have hq1 : (k / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1
    set tk := ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n))
    constructor
    · rw [(inOut_of_V9 (Nat.le_add_right _ _) (by rw [hV10]; exact Nat.add_lt_add_left hq1 _)).2,
          Nat.add_sub_cancel_left]
      rcases List.mem_map.mp ((dftIdx_mod_right_iff h2J hL1 hq1 hk).mp rfl) with ⟨m, hm, hm_eq⟩
      exact List.mem_map.mpr ⟨m, hm, by omega⟩
    · by_cases htk : tk < 2 * n
      · simp only [htk, ↓reduceIte]
        rw [(inOut_of_V11 (Nat.le_add_right _ _) (by rw [hV12]; exact Nat.add_lt_add_left htk _)).1,
            Nat.add_sub_cancel_left]
        exact List.mem_map.mpr ⟨k, (ovlTargetBit_eq_iff hJ hk_L).mp rfl, by omega⟩
      · simp only [htk, ↓reduceIte]
        rw [(inOut_of_V10 (Nat.le_add_right _ _) (by rw [hV11]; exact Nat.add_lt_add_left hk_L _)).1]
        dsimp only
        rw [Nat.add_sub_cancel_left]
        have htk_raw : ¬(ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n) := htk
        simp only [htk_raw, ↓reduceIte, List.mem_singleton]; omega
  by_cases he12 : e < netE12 n
  · rw [rawEnds_of_B11 (by omega) he12]
    have hE12 : netE12 n = netE11 n + 2 * n := rfl
    have hV12 : netV12 n = netV11 n + 2 * n := rfl
    have hV13 : netV13 n = netV12 n + n := rfl
    dsimp [endsB11]
    set k := e - netE11 n
    have hk : k < 2 * n := by omega
    have hn_pos : 0 < n := by omega
    set i := k % n
    have hi : i < n := Nat.mod_lt k hn_pos
    constructor
    · rw [(inOut_of_V11 (Nat.le_add_right _ _) (by rw [hV12]; exact Nat.add_lt_add_left hk _)).2,
          Nat.add_sub_cancel_left, List.mem_singleton]; omega
    · rw [(inOut_of_V12 (Nat.le_add_right _ _) (by rw [hV13]; exact Nat.add_lt_add_left hi _)).1,
          Nat.add_sub_cancel_left]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      by_cases hkn : k < n
      · right; left; have : i = k := Nat.mod_eq_of_lt hkn; omega
      · right; right
        have hsub_lt : k - n < n := by omega
        have hk_eq : k = (k - n) + n := by omega
        have hi_eq : i = k - n := by dsimp [i]; rw [hk_eq, Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]; omega
        omega
  by_cases he13 : e < netE13 n
  · rw [rawEnds_of_B12 (by omega) he13]
    set r := treeLog n + 1
    have hE13 : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl
    have hV16 : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
    have hV18 : netV18 n = netV17 n + (r + 1) := rfl
    set locE := e - netE12 n
    have hlocE : locE < treeEdgeOff r (r + 1) := by omega
    obtain ⟨hj1, hjr, hnode, hw, hlocE_eq⟩ := decodeTreeEdge_spec hlocE
    set te := decodeTreeEdge r locE
    set j := te.1; set node := te.2.1; set w := te.2.2
    have hte : decodeTreeEdge (treeLog n + 1) locE = (j, node, w) :=
      Prod.ext rfl (Prod.ext rfl rfl)
    rw [endsB12_of_decode hte]; dsimp only
    constructor
    · by_cases hw0 : w = 0
      · simp only [hw0, ↓reduceIte]
        have hlocV_lt := encodeTreeVert_lt hj1 hjr hnode (u := 0) (by omega)
        set src := netV15 n + (treeVertOff r j + node * (j + 1) + 0)
        have hsrc_eq : netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) = src := by dsimp [src, r]; omega
        have hdec : decodeTreeVert r (src - netV15 n) = (j, node, 0) := by
          rw [Nat.add_sub_cancel_left]; exact decodeTreeVert_encode hj1 hjr hnode (by omega)
        rw [hsrc_eq, outEdges_of_V15 (Nat.le_add_right _ _) (by rw [hV16]; exact Nat.add_lt_add_left hlocV_lt _) hdec]
        dsimp only; simp only [↓reduceIte, List.mem_singleton]
        change locE = treeEdgeOff r j + node * (2 * j + 1) + w at hlocE_eq
        change e = netE12 n + treeEdgeOff r j + node * (2 * j + 1); omega
      · simp only [hw0, ↓reduceIte]
        set b := (w - 1) / 2
        have hb_lt : b < j := by omega
        have hlocV_lt := encodeTreeVert_lt hj1 hjr hnode (u := 1 + b) (by omega)
        set src := netV15 n + (treeVertOff r j + node * (j + 1) + (1 + b))
        have hsrc_eq : netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) + 1 + b = src := by
          dsimp [src, r]; omega
        have hdec : decodeTreeVert r (src - netV15 n) = (j, node, 1 + b) := by
          rw [Nat.add_sub_cancel_left]; exact decodeTreeVert_encode hj1 hjr hnode (by omega)
        rw [hsrc_eq, outEdges_of_V15 (Nat.le_add_right _ _) (by rw [hV16]; exact Nat.add_lt_add_left hlocV_lt _) hdec]; dsimp only
        simp only [show ¬(1 + b = 0) by omega, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
        change locE = treeEdgeOff r j + node * (2 * j + 1) + w at hlocE_eq
        have hdm : 2 * b + (w - 1) % 2 = w - 1 := Nat.div_add_mod (w - 1) 2
        dsimp [r] at *; omega
    · by_cases hcin : w % 2 = 0 ∧ w < 2 * j
      · simp only [hcin, and_self, ↓reduceIte]
        set b := w / 2
        have hb_lt : b < j := by omega
        have hlocV_lt := encodeTreeVert_lt hj1 hjr hnode (u := 1 + b) (by omega)
        set dst := netV15 n + (treeVertOff r j + node * (j + 1) + (1 + b))
        have hdst_eq : netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) + 1 + b = dst := by
          dsimp [dst, r]; omega
        have hdec : decodeTreeVert r (dst - netV15 n) = (j, node, 1 + b) := by
          rw [Nat.add_sub_cancel_left]; exact decodeTreeVert_encode hj1 hjr hnode (by omega)
        rw [hdst_eq, inEdges_of_V15 (Nat.le_add_right _ _) (by rw [hV16]; exact Nat.add_lt_add_left hlocV_lt _) hdec]; dsimp only
        have he_cin : e = netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b := by
          change locE = treeEdgeOff r j + node * (2 * j + 1) + w at hlocE_eq
          have hdm : 2 * b + w % 2 = w := Nat.div_add_mod w 2
          dsimp [r] at *; omega
        simp only [show ¬(1 + b = 0) by omega, ↓reduceIte, show 1 + b - 1 = b by omega]
        split_ifs <;> simp [he_cin]
      · simp only [hcin, ↓reduceIte]
        set bitIdx := if w = 2 * j then j else w / 2
        have hbit_le : bitIdx ≤ j := by dsimp [bitIdx]; split_ifs <;> omega
        have hw_sw : w = sumWireLoc j bitIdx := (sumWireLoc_iff hj1 hw hbit_le).mp ⟨hcin, rfl⟩
        by_cases hj_lt : j < treeLog n + 1
        · simp only [hj_lt, ↓reduceIte]
          have hnode2 : node / 2 < 2 ^ (r - (j + 1)) := by
            have hexp : r - j = (r - (j + 1)) + 1 := by dsimp [r]; omega
            rw [hexp, pow_succ'] at hnode; omega
          have hlocV_lt := encodeTreeVert_lt (r := r) (j := j + 1) (node := node / 2)
            (u := 1 + bitIdx) (by omega) (by dsimp [r]; omega) hnode2 (by omega)
          have hjj : j + 1 + 1 = j + 2 := by omega
          rw [hjj] at hlocV_lt
          set dst := netV15 n + (treeVertOff r (j + 1) + (node / 2) * (j + 2) + (1 + bitIdx))
          have hdst_eq : netV15 n + treeVertOff (treeLog n + 1) (j + 1) + (node / 2) * (j + 2) + 1 + bitIdx = dst := by
            dsimp [dst, r]; omega
          have hdec : decodeTreeVert r (dst - netV15 n) = (j + 1, node / 2, 1 + bitIdx) := by
            dsimp [dst]; rw [Nat.add_sub_cancel_left, ← hjj]
            exact decodeTreeVert_encode (by omega) (by dsimp [r]; omega) hnode2 (by omega)
          rw [hdst_eq, inEdges_of_V15 (Nat.le_add_right _ _) (by rw [hV16]; exact Nat.add_lt_add_left hlocV_lt _) hdec]
          dsimp only
          simp only [show ¬(1 + bitIdx = 0) by omega, show ¬(j + 1 = 1) by omega, ↓reduceIte,
                     show 1 + bitIdx - 1 = bitIdx by omega, show j + 1 - 1 = j by omega,
                     List.mem_cons, List.not_mem_nil, or_false]
          change locE = treeEdgeOff r j + node * (2 * j + 1) + w at hlocE_eq
          rw [← hw_sw]
          have hdm := Nat.div_add_mod node 2
          rcases (show node % 2 = 0 ∨ node % 2 = 1 by omega) with hm0 | hm1
          · left
            have hnode_eq : 2 * (node / 2) = node := by omega
            rw [hnode_eq]; dsimp [r] at hlocE_eq ⊢; omega
          · right; left
            have hnode_eq : 2 * (node / 2) + 1 = node := by omega
            rw [hnode_eq]; dsimp [r] at hlocE_eq ⊢; omega
        · simp only [hj_lt, ↓reduceIte]
          have hj_eq_r : j = r := by dsimp [r]; omega
          have hnode0 : node = 0 := by rw [hj_eq_r, Nat.sub_self, pow_zero] at hnode; omega
          have hbit_lt : bitIdx < r + 1 := Nat.lt_succ_of_le (hj_eq_r ▸ hbit_le)
          rw [(inOut_of_V17 (Nat.le_add_right _ _) (by rw [hV18]; exact Nat.add_lt_add_left hbit_lt _)).1,
              Nat.add_sub_cancel_left]
          simp only [List.mem_cons, List.not_mem_nil, or_false]; left
          change locE = treeEdgeOff r j + node * (2 * j + 1) + w at hlocE_eq
          rw [hw_sw, hj_eq_r, hnode0, Nat.zero_mul, Nat.add_zero] at hlocE_eq
          dsimp [locE, r] at hlocE_eq ⊢; omega
  rw [rawEnds_of_B13 (by omega)]
  set W := treeLog n + 2
  have hE14 : netEdgeCount n = netE13 n + (W + 1) := rfl
  have hV17 : netV17 n = netV16 n + 1 := rfl
  have hV18 : netV18 n = netV17 n + W := rfl
  set b := e - netE13 n
  have hb_lt : b < W + 1 := by omega
  dsimp [endsB13]
  change e ∈ outEdges n (if b = 0 then netV16 n else netV17 n + (b - 1)) ∧
    e ∈ inEdges n (if b < W then netV17 n + b else netV18 n)
  constructor
  · by_cases hb0 : b = 0
    · simp only [hb0, ↓reduceIte]
      rw [(inOut_of_V16 le_rfl (by omega)).2, List.mem_singleton]; omega
    · simp only [hb0, ↓reduceIte]
      rw [(inOut_of_V17 (by omega) (by omega)).2, Nat.add_sub_cancel_left, List.mem_singleton]; omega
  · by_cases hbW : b < W
    · simp only [hbW, ↓reduceIte]
      rw [(inOut_of_V17 (by omega) (by omega)).1, Nat.add_sub_cancel_left]
      simp only [List.mem_cons, List.not_mem_nil, or_false]; right; omega
    · simp only [hbW, ↓reduceIte]
      rw [(inOut_of_V18 le_rfl).1, List.mem_singleton]; dsimp [W] at hbW hb_lt; omega

lemma rawEnds_mem_inOutEdges (n e : ℕ) (he : e < netEdgeCount n) :
    e ∈ outEdges n (rawEnds n e).1 ∧ e ∈ inEdges n (rawEnds n e).2 := by
  by_cases he8 : e < netE8 n
  · exact rawEnds_mem_0_7 n e he8
  · exact rawEnds_mem_8_13 n e (by omega) he

/-! ### Exact `QCSD_incidentList` Characterization via `expectedInc` -/

lemma expectedInc_spec (n v : ℕ) (hv : v < netVertCount n) :
    (expectedInc n v).Pairwise (· < ·) ∧
    (∀ e ∈ expectedInc n v, e < netEdgeCount n) ∧
    (∀ e < netEdgeCount n, e ∈ expectedInc n v ↔ (rawEnds n e).1 = v ∨ (rawEnds n e).2 = v) := by
  obtain ⟨hp_in, hp_out, hsep, hin_end, hout_end⟩ := inOutEdges_spec n v hv
  refine ⟨pairwise_lt_append hp_in hp_out hsep, ?_, ?_⟩
  · intro e he
    rw [expectedInc, List.mem_append] at he
    rcases he with he | he
    · exact (hin_end e he).1
    · exact (hout_end e he).1
  · intro e he
    rw [expectedInc, List.mem_append]
    constructor
    · rintro (hin | hout)
      · exact Or.inr (hin_end e hin).2
      · exact Or.inl (hout_end e hout).2
    · rintro (hfst | hsnd)
      · subst hfst; exact Or.inr (rawEnds_mem_inOutEdges n e he).1
      · subst hsnd; exact Or.inl (rawEnds_mem_inOutEdges n e he).2

def listToFin {k : ℕ} : (l : List ℕ) → (∀ x ∈ l, x < k) → List (Fin k)
  | [], _ => []
  | a :: as, h =>
    ⟨a, h a List.mem_cons_self⟩ ::
      listToFin as (fun x hx => h x (List.mem_cons_of_mem a hx))

lemma listToFin_length {k : ℕ} : ∀ (l : List ℕ) (h : ∀ x ∈ l, x < k),
    (listToFin l h).length = l.length
  | [], _ => rfl
  | _ :: as, h => by simp [listToFin, listToFin_length as]

lemma listToFin_mem {k : ℕ} : ∀ (l : List ℕ) (h : ∀ x ∈ l, x < k) (e : Fin k),
    e ∈ listToFin l h ↔ e.val ∈ l
  | [], _, _ => by simp [listToFin]
  | a :: as, h, e => by
    simp only [listToFin, List.mem_cons, listToFin_mem as, Fin.ext_iff]

lemma listToFin_pairwise {k : ℕ} : ∀ (l : List ℕ) (h : ∀ x ∈ l, x < k),
    l.Pairwise (· < ·) → (listToFin l h).Pairwise (· < ·)
  | [], _, _ => by simp [listToFin]
  | a :: as, h, hp => by
    rw [List.pairwise_cons] at hp
    simp only [listToFin, List.pairwise_cons]
    refine ⟨?_, listToFin_pairwise as _ hp.2⟩
    intro e he
    rw [listToFin_mem] at he
    exact hp.1 e.val he

lemma listToFin_get_val {k : ℕ} : ∀ (l : List ℕ) (h : ∀ x ∈ l, x < k)
    (i : ℕ) (hi : i < (listToFin l h).length),
    ((listToFin l h).get ⟨i, hi⟩).val = l.getD i 0
  | [], _, _, hi => by simp [listToFin] at hi
  | a :: as, h, 0, _ => by simp [listToFin]
  | a :: as, h, i + 1, hi => by
    simp only [listToFin, List.get_eq_getElem, List.getElem_cons_succ, List.getD_cons_succ]
    exact listToFin_get_val as _ i (by simpa [listToFin] using hi)

theorem incidentList_netEnds (n : ℕ) (v : Fin (netVertCount n)) :
    QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v =
      listToFin (expectedInc n v.val) (expectedInc_spec n v.val v.isLt).2.1 := by
  obtain ⟨hpw, hbnd, hmem⟩ := expectedInc_spec n v.val v.isLt
  apply incidentList_eq_of_strictMono
  · exact listToFin_pairwise _ hbnd hpw
  · intro e
    rw [listToFin_mem, hmem e.val e.isLt]
    simp [netEnds, Fin.ext_iff]

lemma deg_netEnds (n : ℕ) (v : Fin (netVertCount n)) :
    (QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v).length =
      (expectedInc n v.val).length := by
  rw [incidentList_netEnds, listToFin_length]

def wireAt (n : ℕ) (x : Fin (netEdgeCount n) → Bool) (e : ℕ) : Bool :=
  if h : e < netEdgeCount n then x ⟨e, h⟩ else false

lemma wireAt_lt {n : ℕ} (x : Fin (netEdgeCount n) → Bool) {e : ℕ} (he : e < netEdgeCount n) :
    wireAt n x e = x ⟨e, he⟩ := by
  simp [wireAt, he]

/-! ### Explicit Vertex Predicate `rawPred`, Network Assembly (`N_exact`, `N_sep`, `N_le`), and `QCSD_TCClass2` -/

/-- Explicit TM-friendly vertex circuit constructor (`mode = 0` Exact, `mode = 1` Le, `mode = 2` Sep).
    Notice:
    1. Zero calls to `QCSD_incidentList`.
    2. Only `v < 2 * n` (`v < netV1 n`) inspects `pre`! -/
def rawPred (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) (v : ℕ) :
    QCSD_BoolCircuit :=
  let J := paramJ n
  let L := paramL n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let r := treeLog n + 1
  let W := treeLog n + 2
  if v < netV1 n then
    pinBitCircuit (if v < pre.length then some (pre.getD v false) else none)
  else if v < netV2 n then
    linearMapCheckCircuit 1 2 (fun _ _ => true)
  else if v < netV3 n then
    let idx := v - netV2 n
    pinBitCircuit (some (if hlt : idx < n then zmod2ToBool (h ⟨idx, hlt⟩) else false))
  else if v < netV4 n then
    let inList := fwdSt1InIndices n J L2 (v - netV3 n)
    linearMapCheckCircuit inList.length (2 * J * L1) (fwdSt1Mat J L1 (paramOmegaExp n) inList)
  else if v < netV5 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramOmegaExp n))
  else if v < netV6 n then
    let inList := fwdSt1InIndices n J L2 (v - netV5 n)
    linearMapCheckCircuit inList.length (2 * J * L1) (fwdSt1Mat J L1 (paramOmegaExp n) inList)
  else if v < netV7 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramOmegaExp n))
  else if v < netV8 n then
    bilinearMapCheckCircuit (2 * J) (2 * J) (2 * J) (ringMulTensor J)
  else if v < netV9 n then
    linearMapCheckCircuit (2 * J * L1) (2 * J * L1)
      (fullSt1Mat J L1 L2 (paramInvOmegaExp n) (v - netV8 n))
  else if v < netV10 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramInvOmegaExp n))
  else if v < netV11 n then
    let k := v - netV10 n
    constCircuit (if ovlTargetBit J (k / (2 * J)) (k % (2 * J)) < 2 * n then 0 else 1) true
  else if v < netV12 n then
    let dIn := (ovlInLocal J L (v - netV11 n)).length
    linearMapCheckCircuit dIn 1 (fun _ _ => true)
  else if v < netV13 n then
    let i := v - netV12 n
    synCheckCircuit (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false)
  else if v < netV14 n then
    pinBitCircuit (some false)
  else if v < netV15 n then
    pinBitCircuit (some false)
  else if v < netV16 n then
    let tv := decodeTreeVert r (v - netV15 n)
    let j := tv.1; let u := tv.2.2
    if u = 0 then pinBitCircuit (some false)
    else
      let b := u - 1
      if mode = 2 ∧ j = r then
        sepFullAdderCircuit (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
      else fullAdderCircuit
  else if v < netV17 n then
    pinBitCircuit (some false)
  else if v < netV18 n then
    let b := v - netV17 n
    if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b)
    else if mode = 1 then borrowStepCircuit (t0.testBit b)
    else sepCmpStepCircuit
  else
    if mode = 1 ∧ ¬(t0 < 2 ^ W) then constCircuit 1 true
    else pinBitCircuit (some false)

lemma rawPred_pre_indep (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre1 pre2 : List Bool) {v : ℕ} (hv : 2 * n ≤ v) :
    rawPred mode n h s t0 t1 pre1 v = rawPred mode n h s t0 t1 pre2 v := by
  have hnlt : ¬(v < netV1 n) := by change ¬(v < 2 * n); omega
  unfold rawPred; dsimp only
  simp only [hnlt, ↓reduceIte]

lemma rawPred_of_V0 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hhi : v < netV1 n) :
    rawPred mode n h s t0 t1 pre v =
      pinBitCircuit (if v < pre.length then some (pre.getD v false) else none) := by
  unfold rawPred; dsimp only; simp only [hhi, ↓reduceIte]

lemma rawPred_of_V1 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV1 n ≤ v) (hhi : v < netV2 n) :
    rawPred mode n h s t0 t1 pre v = linearMapCheckCircuit 1 2 (fun _ _ => true) := by
  unfold rawPred; dsimp only; simp only [show ¬(v < netV1 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V2 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV2 n ≤ v) (hhi : v < netV3 n) :
    rawPred mode n h s t0 t1 pre v =
      pinBitCircuit (some (if hlt : v - netV2 n < n then zmod2ToBool (h ⟨v - netV2 n, hlt⟩) else false)) := by
  rcases netV_chain n with ⟨_, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V3 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV3 n ≤ v) (hhi : v < netV4 n) :
    rawPred mode n h s t0 t1 pre v =
      (let inList := fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)
       linearMapCheckCircuit inList.length (2 * paramJ n * paramL1 n)
         (fwdSt1Mat (paramJ n) (paramL1 n) (paramOmegaExp n) inList)) := by
  rcases netV_chain n with ⟨_, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V4 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV4 n ≤ v) (hhi : v < netV5 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V5 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV5 n ≤ v) (hhi : v < netV6 n) :
    rawPred mode n h s t0 t1 pre v =
      (let inList := fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)
       linearMapCheckCircuit inList.length (2 * paramJ n * paramL1 n)
         (fwdSt1Mat (paramJ n) (paramL1 n) (paramOmegaExp n) inList)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V6 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV6 n ≤ v) (hhi : v < netV7 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V7 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV7 n ≤ v) (hhi : v < netV8 n) :
    rawPred mode n h s t0 t1 pre v =
      bilinearMapCheckCircuit (2 * paramJ n) (2 * paramJ n) (2 * paramJ n) (ringMulTensor (paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V8 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV8 n ≤ v) (hhi : v < netV9 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL1 n) (2 * paramJ n * paramL1 n)
        (fullSt1Mat (paramJ n) (paramL1 n) (paramL2 n) (paramInvOmegaExp n) (v - netV8 n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V9 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV9 n ≤ v) (hhi : v < netV10 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramInvOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V10 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV10 n ≤ v) (hhi : v < netV11 n) :
    rawPred mode n h s t0 t1 pre v =
      (let k := v - netV10 n
       constCircuit (if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
                     then 0 else 1) true) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V11 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV11 n ≤ v) (hhi : v < netV12 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) (v - netV11 n)).length 1 (fun _ _ => true) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V12 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV12 n ≤ v) (hhi : v < netV13 n) :
    rawPred mode n h s t0 t1 pre v =
      synCheckCircuit (if hlt : v - netV12 n < n then zmod2ToBool (s ⟨v - netV12 n, hlt⟩) else false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V13 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV13 n ≤ v) (hhi : v < netV14 n) :
    rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V14 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV14 n ≤ v) (hhi : v < netV15 n) :
    rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V15 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    {v j node u : ℕ} (hlo : netV15 n ≤ v) (hhi : v < netV16 n)
    (hdec : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (j, node, u)) :
    rawPred mode n h s t0 t1 pre v =
      (let r := treeLog n + 1
       if u = 0 then pinBitCircuit (some false)
       else
         let b := u - 1
         if mode = 2 ∧ j = r then
           sepFullAdderCircuit (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
         else fullAdderCircuit) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, hhi, ↓reduceIte, hdec]

lemma rawPred_of_V16 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV16 n ≤ v) (hhi : v < netV17 n) :
    rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V17 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV17 n ≤ v) (hhi : v < netV18 n) :
    rawPred mode n h s t0 t1 pre v =
      (let b := v - netV17 n
       let W := treeLog n + 2
       if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b)
       else if mode = 1 then borrowStepCircuit (t0.testBit b)
       else sepCmpStepCircuit) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, hhi, ↓reduceIte]

lemma rawPred_of_V18 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV18 n ≤ v) :
    rawPred mode n h s t0 t1 pre v =
      (if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then constCircuit 1 true
       else pinBitCircuit (some false)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, show ¬(v < netV18 n) by omega, ↓reduceIte]

lemma rawPred_arity_and_wf_0_9 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (v : ℕ) (hv10 : v < netV10 n) :
    (rawPred mode n h s t0 t1 pre v).numInputs = (expectedInc n v).length ∧
    QCSD_circuitWF (rawPred mode n h s t0 t1 pre v) := by
  have h2J : 0 < 2 * paramJ n := by have := paramJ_pos n; omega
  unfold expectedInc
  by_cases hv1 : v < netV1 n
  · rw [rawPred_of_V0 _ _ _ _ _ _ _ hv1, (inOut_of_V0 hv1).1, (inOut_of_V0 hv1).2]
    exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
  by_cases hv2 : v < netV2 n
  · rw [rawPred_of_V1 _ _ _ _ _ _ _ (by omega) hv2, (inOut_of_V1 (by omega) hv2).1, (inOut_of_V1 (by omega) hv2).2]
    exact ⟨rfl, (linearMapCheckCircuit_spec 1 2 _ (fun _ => false)).1⟩
  by_cases hv3 : v < netV3 n
  · rw [rawPred_of_V2 _ _ _ _ _ _ _ (by omega) hv3, (inOut_of_V2 (by omega) hv3).1, (inOut_of_V2 (by omega) hv3).2]
    exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
  by_cases hv4 : v < netV4 n
  · rw [rawPred_of_V3 _ _ _ _ _ _ _ (by omega) hv4, (inOut_of_V3 (by omega) hv4).1, (inOut_of_V3 (by omega) hv4).2]
    dsimp only
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  by_cases hv5 : v < netV5 n
  · rw [rawPred_of_V4 _ _ _ _ _ _ _ (by omega) hv5, (inOut_of_V4 (by omega) hv5).1, (inOut_of_V4 (by omega) hv5).2]
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  by_cases hv6 : v < netV6 n
  · rw [rawPred_of_V5 _ _ _ _ _ _ _ (by omega) hv6, (inOut_of_V5 (by omega) hv6).1, (inOut_of_V5 (by omega) hv6).2]
    dsimp only
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  by_cases hv7 : v < netV7 n
  · rw [rawPred_of_V6 _ _ _ _ _ _ _ (by omega) hv7, (inOut_of_V6 (by omega) hv7).1, (inOut_of_V6 (by omega) hv7).2]
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  by_cases hv8 : v < netV8 n
  · rw [rawPred_of_V7 _ _ _ _ _ _ _ (by omega) hv8, (inOut_of_V7 (by omega) hv8).1, (inOut_of_V7 (by omega) hv8).2]
    exact ⟨by simp [bilinearMapCheckCircuit_numInputs]; omega,
      (bilinearMapCheckCircuit_spec _ _ _ _ h2J (fun _ => false)).1⟩
  by_cases hv9 : v < netV9 n
  · rw [rawPred_of_V8 _ _ _ _ _ _ _ (by omega) hv9, (inOut_of_V8 (by omega) hv9).1, (inOut_of_V8 (by omega) hv9).2]
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  rw [rawPred_of_V9 _ _ _ _ _ _ _ (by omega) hv10, (inOut_of_V9 (by omega) hv10).1, (inOut_of_V9 (by omega) hv10).2]
  exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩

lemma ite_pos {α : Sort*} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := by
  cases inst with
  | isFalse h => exact absurd hc h
  | isTrue _ => rfl

lemma ite_neg {α : Sort*} {c : Prop} [inst : Decidable c] (hc : ¬c) {a b : α} :
    (if c then a else b) = b := by
  cases inst with
  | isFalse _ => rfl
  | isTrue h => exact absurd h hc

lemma dite_pos {α : Sort*} {c : Prop} [inst : Decidable c] (hc : c) {t : c → α} {e : ¬c → α} :
    dite c t e = t hc := by
  cases inst with
  | isFalse h => exact absurd hc h
  | isTrue _ => rfl

lemma rawPred_arity_and_wf (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (v : ℕ) (_hv : v < netVertCount n) :
    (rawPred mode n h s t0 t1 pre v).numInputs = (expectedInc n v).length ∧
    QCSD_circuitWF (rawPred mode n h s t0 t1 pre v) := by
  by_cases hv10 : v < netV10 n
  · exact rawPred_arity_and_wf_0_9 mode n h s t0 t1 pre v hv10
  unfold expectedInc
  by_cases hv11 : v < netV11 n
  · rw [rawPred_of_V10 _ _ _ _ _ _ _ (by omega) hv11, (inOut_of_V10 (by omega) hv11).1, (inOut_of_V10 (by omega) hv11).2]
    dsimp only; refine ⟨by split_ifs <;> rfl, constCircuit_wf _ true⟩
  by_cases hv12 : v < netV12 n
  · rw [rawPred_of_V11 _ _ _ _ _ _ _ (by omega) hv12, (inOut_of_V11 (by omega) hv12).1, (inOut_of_V11 (by omega) hv12).2]
    exact ⟨by simp [linearMapCheckCircuit_numInputs], (linearMapCheckCircuit_spec _ _ _ (fun _ => false)).1⟩
  by_cases hv13 : v < netV13 n
  · rw [rawPred_of_V12 _ _ _ _ _ _ _ (by omega) hv13, (inOut_of_V12 (by omega) hv13).1, (inOut_of_V12 (by omega) hv13).2]
    exact ⟨rfl, (synCheckCircuit_wf_and_eval _ (fun _ => false)).1⟩
  by_cases hv14 : v < netV14 n
  · rw [rawPred_of_V13 _ _ _ _ _ _ _ (by omega) hv14, (inOut_of_V13 (by omega) hv14).1, (inOut_of_V13 (by omega) hv14).2]
    exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
  by_cases hv15 : v < netV15 n
  · rw [rawPred_of_V14 _ _ _ _ _ _ _ (by omega) hv15, (inOut_of_V14 (by omega) hv15).1, (inOut_of_V14 (by omega) hv15).2]
    exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
  by_cases hv16 : v < netV16 n
  · set tv := decodeTreeVert (treeLog n + 1) (v - netV15 n)
    have htv : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (tv.1, tv.2.1, tv.2.2) :=
      Prod.ext rfl (Prod.ext rfl rfl)
    rw [rawPred_of_V15 _ _ _ _ _ _ _ (by omega) hv16 htv,
        inEdges_of_V15 (by omega) hv16 htv, outEdges_of_V15 (by omega) hv16 htv]
    dsimp only
    by_cases hu0 : tv.2.2 = 0
    · simp only [hu0, ↓reduceIte]
      exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
    · simp only [hu0, ↓reduceIte]
      have hlen3 : (if tv.1 = 1 then
            [netE2 n + 2 * tv.2.1, netE2 n + 2 * tv.2.1 + 1,
             netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1)]
          else
            [netE12 n + treeEdgeOff (treeLog n + 1) (tv.1 - 1) + 2 * tv.2.1 * (2 * (tv.1 - 1) + 1) +
               sumWireLoc (tv.1 - 1) (tv.2.2 - 1),
             netE12 n + treeEdgeOff (treeLog n + 1) (tv.1 - 1) + (2 * tv.2.1 + 1) * (2 * (tv.1 - 1) + 1) +
               sumWireLoc (tv.1 - 1) (tv.2.2 - 1),
             netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1)]).length = 3 := by
        split_ifs <;> rfl
      by_cases hsep : mode = 2 ∧ tv.1 = treeLog n + 1
      · rw [ite_pos hsep, List.length_append, hlen3]
        exact ⟨sepFullAdderCircuit_numInputs _ _ _, (sepFullAdderCircuit_spec _ _ _ (fun _ => false)).1⟩
      · rw [ite_neg hsep, List.length_append, hlen3]
        exact ⟨rfl, (fullAdderCircuit_wf_and_eval (fun _ => false)).1⟩
  by_cases hv17 : v < netV17 n
  · rw [rawPred_of_V16 _ _ _ _ _ _ _ (by omega) hv17, (inOut_of_V16 (by omega) hv17).1, (inOut_of_V16 (by omega) hv17).2]
    exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩
  by_cases hv18 : v < netV18 n
  · rw [rawPred_of_V17 _ _ _ _ _ _ _ (by omega) hv18, (inOut_of_V17 (by omega) hv18).1, (inOut_of_V17 (by omega) hv18).2]
    dsimp only; split_ifs
    · exact ⟨exactCmpStepCircuit_numInputs _ _, (exactCmpStepCircuit_spec _ _ (fun _ => false)).1⟩
    · exact ⟨rfl, (borrowStepCircuit_wf_and_eval _ (fun _ => false)).1⟩
    · exact ⟨rfl, (sepCmpStepCircuit_spec (fun _ => false)).1⟩
  rw [rawPred_of_V18 _ _ _ _ _ _ _ (by omega), (inOut_of_V18 (by omega)).1, (inOut_of_V18 (by omega)).2]
  split_ifs
  · exact ⟨rfl, constCircuit_wf 1 true⟩
  · exact ⟨pinBitCircuit_numInputs _, pinBitCircuit_wf _⟩

lemma linearMapCheckCircuit_size_le_sq {numIn numOut S : ℕ} (mat : ℕ → ℕ → Bool)
    (hS : 1 ≤ S) (hin : numIn ≤ S) (hout : numOut ≤ S) :
    QCSD_circuitSize (linearMapCheckCircuit numIn numOut mat) ≤ 500 * S ^ 2 := by
  have hb := (linearMapCheckCircuit_spec numIn numOut mat (fun _ => false)).2.2
  have hassoc : 5 * numOut * numIn = 5 * (numOut * numIn) := by ring
  rw [hassoc] at hb
  have hmul : numOut * numIn ≤ S ^ 2 := by
    calc numOut * numIn ≤ S * S := Nat.mul_le_mul hout hin
         _ = S ^ 2 := by ring
  have hS_sq : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 2 by decide)
  have h1_sq : 1 ≤ S ^ 2 := Nat.one_le_pow 2 S hS
  omega

lemma bilinearRingMul_size_le_sq {n : ℕ} (hn : 1 ≤ n) :
    QCSD_circuitSize (bilinearMapCheckCircuit (2 * paramJ n) (2 * paramJ n) (2 * paramJ n)
      (ringMulTensor (paramJ n))) ≤ 500 * (netEdgeCount n) ^ 2 := by
  have hJ_pos : 0 < paramJ n := paramJ_pos n
  rcases netE_chain n with
    ⟨_, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hE1 : netE1 n = 2 * n := rfl
  have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
  have hL_pos : 1 ≤ paramL n := Nat.one_le_pow _ 3 (by decide)
  have h2J_le_S : 2 * paramJ n ≤ netEdgeCount n := by
    have : 2 * paramJ n * 1 ≤ 2 * paramJ n * paramL n := Nat.mul_le_mul_left _ hL_pos
    omega
  have hn_le_S : n ≤ netEdgeCount n := by omega
  have hS_pos : 1 ≤ netEdgeCount n := by omega
  have hS_sq : netEdgeCount n ≤ (netEdgeCount n) ^ 2 := by
    simpa using Nat.pow_le_pow_right hS_pos (show 1 ≤ 2 by decide)
  have h1_sq : 1 ≤ (netEdgeCount n) ^ 2 := Nat.one_le_pow 2 (netEdgeCount n) hS_pos
  have hJ2 : (paramJ n) ^ 2 ≤ 9 * netEdgeCount n := by
    have := paramJ_sq_lt_nine_mul hn; omega
  have hJ3 : (paramJ n) ^ 3 ≤ 9 * (netEdgeCount n) ^ 2 := by
    calc (paramJ n) ^ 3 = paramJ n * (paramJ n) ^ 2 := by ring
         _ ≤ netEdgeCount n * (9 * netEdgeCount n) := Nat.mul_le_mul (by omega) hJ2
         _ = 9 * (netEdgeCount n) ^ 2 := by ring
  have hb := (bilinearMapCheckCircuit_spec (2 * paramJ n) (2 * paramJ n) (2 * paramJ n)
    (ringMulTensor (paramJ n)) (by omega) (fun _ => false)).2.2
  have hlin : 2 + 2 * (2 * paramJ n + 2 * paramJ n) + 10 * (2 * paramJ n) +
      (2 * paramJ n) * (2 * paramJ n) + 5 * (2 * paramJ n) * ((2 * paramJ n) * (2 * paramJ n)) =
      2 + 28 * paramJ n + 4 * (paramJ n) ^ 2 + 40 * (paramJ n) ^ 3 := by ring
  rw [hlin] at hb
  have hJ_sq : paramJ n ≤ (netEdgeCount n) ^ 2 := by omega
  have hJ2_sq : (paramJ n) ^ 2 ≤ 9 * (netEdgeCount n) ^ 2 := by omega
  omega

lemma rawPred_size_and_deg_0_9 {n : ℕ} (hn : 1 ≤ n)
    (mode : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : ℕ) (hv10 : v < netV10 n) :
    QCSD_circuitSize (rawPred mode n h s t0 t1 pre v) ≤ 500 * (netEdgeCount n) ^ 2 ∧
    ((expectedInc n v).length) ^ 4 ≤ 63 ^ 4 * (netEdgeCount n) ^ 3 := by
  have hJ_pos : 1 ≤ paramJ n := one_le_paramJ n
  have hL1_pos : 1 ≤ paramL1 n := one_le_paramL1 n
  have hL2_pos : 1 ≤ paramL2 n := one_le_paramL2 n
  have hL1_le_L2 : paramL1 n ≤ paramL2 n := paramL1_le_paramL2 n
  have hL_mul : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  rcases netE_chain n with
    ⟨_, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hE1 : netE1 n = 2 * n := rfl
  have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
  have hn_le_S : n ≤ netEdgeCount n := by omega
  have hS_pos : 1 ≤ netEdgeCount n := by omega
  have h1_sq : 1 ≤ (netEdgeCount n) ^ 2 := Nat.one_le_pow 2 (netEdgeCount n) hS_pos
  have hJL_le_S : 2 * paramJ n * paramL n ≤ netEdgeCount n := by omega
  have h2JL1_le_S : 2 * paramJ n * paramL1 n ≤ netEdgeCount n := by
    have : 2 * paramJ n * paramL1 n * 1 ≤ 2 * paramJ n * paramL1 n * paramL2 n :=
      Nat.mul_le_mul_left _ hL2_pos
    have hmul : 2 * paramJ n * paramL n = 2 * paramJ n * paramL1 n * paramL2 n := by
      rw [hL_mul]; ring
    omega
  have h2JL2_le_S : 2 * paramJ n * paramL2 n ≤ netEdgeCount n := by
    have : 2 * paramJ n * paramL2 n * 1 ≤ 2 * paramJ n * paramL2 n * paramL1 n :=
      Nat.mul_le_mul_left _ hL1_pos
    have hmul : 2 * paramJ n * paramL n = 2 * paramJ n * paramL2 n * paramL1 n := by
      rw [hL_mul]; ring
    omega
  have hn3_le_S3 : n ^ 3 ≤ (netEdgeCount n) ^ 3 := Nat.pow_le_pow_left hn_le_S 3
  have hd_4JL2 : ∀ d ≤ 4 * paramJ n * paramL2 n, d ^ 4 ≤ 63 ^ 4 * (netEdgeCount n) ^ 3 := fun d hd =>
    le_trans (Nat.pow_le_pow_left hd 4)
      (le_trans (le_of_lt (four_J_L2_pow4_lt hn)) (Nat.mul_le_mul_left _ hn3_le_S3))
  have hd_6J : ∀ d ≤ 6 * paramJ n, d ^ 4 ≤ 63 ^ 4 * (netEdgeCount n) ^ 3 := fun d hd =>
    le_trans (Nat.pow_le_pow_left hd 4)
      (le_trans (le_of_lt (six_J_pow4_lt hn)) (Nat.mul_le_mul_left _ hn3_le_S3))
  have hsmall_size : ∀ c : QCSD_BoolCircuit, QCSD_circuitSize c ≤ 65 →
      QCSD_circuitSize c ≤ 500 * (netEdgeCount n) ^ 2 := fun c hc => by omega
  unfold expectedInc
  by_cases hv1 : v < netV1 n
  · rw [rawPred_of_V0 _ _ _ _ _ _ _ hv1, (inOut_of_V0 hv1).1, (inOut_of_V0 hv1).2]
    exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
  by_cases hv2 : v < netV2 n
  · rw [rawPred_of_V1 _ _ _ _ _ _ _ (by omega) hv2, (inOut_of_V1 (by omega) hv2).1, (inOut_of_V1 (by omega) hv2).2]
    exact ⟨linearMapCheckCircuit_size_le_sq _ hS_pos (by omega) (by omega), hd_6J 3 (by omega)⟩
  by_cases hv3 : v < netV3 n
  · rw [rawPred_of_V2 _ _ _ _ _ _ _ (by omega) hv3, (inOut_of_V2 (by omega) hv3).1, (inOut_of_V2 (by omega) hv3).2]
    exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
  by_cases hv4 : v < netV4 n
  · rw [rawPred_of_V3 _ _ _ _ _ _ _ (by omega) hv4, (inOut_of_V3 (by omega) hv4).1, (inOut_of_V3 (by omega) hv4).2]
    dsimp only
    have hin_len : (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)).length ≤ paramJ n * paramL1 n :=
      fwdSt1InIndices_length_le hn _
    have hin_le_n : (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)).length ≤ n := by
      unfold fwdSt1InIndices; exact le_trans (List.length_filter_le _ _) (by simp)
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos (by omega) h2JL1_le_S, hd_4JL2 _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    calc (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)).length + 2 * paramJ n * paramL1 n
        ≤ paramJ n * paramL1 n + 2 * paramJ n * paramL1 n := Nat.add_le_add_right hin_len _
      _ = 3 * (paramJ n * paramL1 n) := by ring
      _ ≤ 4 * (paramJ n * paramL2 n) := by
          have := Nat.mul_le_mul_left (paramJ n) hL1_le_L2; omega
      _ = 4 * paramJ n * paramL2 n := by ring
  by_cases hv5 : v < netV5 n
  · rw [rawPred_of_V4 _ _ _ _ _ _ _ (by omega) hv5, (inOut_of_V4 (by omega) hv5).1, (inOut_of_V4 (by omega) hv5).2]
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos h2JL2_le_S h2JL2_le_S, hd_4JL2 _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    exact le_of_eq (by ring)
  by_cases hv6 : v < netV6 n
  · rw [rawPred_of_V5 _ _ _ _ _ _ _ (by omega) hv6, (inOut_of_V5 (by omega) hv6).1, (inOut_of_V5 (by omega) hv6).2]
    dsimp only
    have hin_len : (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)).length ≤ paramJ n * paramL1 n :=
      fwdSt1InIndices_length_le hn _
    have hin_le_n : (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)).length ≤ n := by
      unfold fwdSt1InIndices; exact le_trans (List.length_filter_le _ _) (by simp)
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos (by omega) h2JL1_le_S, hd_4JL2 _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    calc (fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)).length + 2 * paramJ n * paramL1 n
        ≤ paramJ n * paramL1 n + 2 * paramJ n * paramL1 n := Nat.add_le_add_right hin_len _
      _ = 3 * (paramJ n * paramL1 n) := by ring
      _ ≤ 4 * (paramJ n * paramL2 n) := by
          have := Nat.mul_le_mul_left (paramJ n) hL1_le_L2; omega
      _ = 4 * paramJ n * paramL2 n := by ring
  by_cases hv7 : v < netV7 n
  · rw [rawPred_of_V6 _ _ _ _ _ _ _ (by omega) hv7, (inOut_of_V6 (by omega) hv7).1, (inOut_of_V6 (by omega) hv7).2]
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos h2JL2_le_S h2JL2_le_S, hd_4JL2 _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    exact le_of_eq (by ring)
  by_cases hv8 : v < netV8 n
  · rw [rawPred_of_V7 _ _ _ _ _ _ _ (by omega) hv8, (inOut_of_V7 (by omega) hv8).1, (inOut_of_V7 (by omega) hv8).2]
    refine ⟨bilinearRingMul_size_le_sq hn, hd_6J _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    exact le_of_eq (by ring)
  by_cases hv9 : v < netV9 n
  · rw [rawPred_of_V8 _ _ _ _ _ _ _ (by omega) hv9, (inOut_of_V8 (by omega) hv9).1, (inOut_of_V8 (by omega) hv9).2]
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos h2JL1_le_S h2JL1_le_S, hd_4JL2 _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_range]
    calc 2 * paramJ n * paramL1 n + 2 * paramJ n * paramL1 n
        = 4 * (paramJ n * paramL1 n) := by ring
      _ ≤ 4 * (paramJ n * paramL2 n) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (paramJ n) hL1_le_L2)
      _ = 4 * paramJ n * paramL2 n := by ring
  rw [rawPred_of_V9 _ _ _ _ _ _ _ (by omega) hv10, (inOut_of_V9 (by omega) hv10).1, (inOut_of_V9 (by omega) hv10).2]
  refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos h2JL2_le_S h2JL2_le_S, hd_4JL2 _ ?_⟩
  simp only [List.length_append, List.length_map, List.length_range]
  exact le_of_eq (by ring)

lemma rawPred_size_and_deg {n : ℕ} (hn : 1 ≤ n)
    (mode : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : ℕ) (_hv : v < netVertCount n) :
    QCSD_circuitSize (rawPred mode n h s t0 t1 pre v) ≤ 500 * (netEdgeCount n) ^ 2 ∧
    ((expectedInc n v).length) ^ 4 ≤ 63 ^ 4 * (netEdgeCount n) ^ 3 := by
  by_cases hv10 : v < netV10 n
  · exact rawPred_size_and_deg_0_9 hn mode h s t0 t1 pre v hv10
  have hJ_pos : 1 ≤ paramJ n := one_le_paramJ n
  rcases netE_chain n with
    ⟨_, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hE1 : netE1 n = 2 * n := rfl
  have hn_le_S : n ≤ netEdgeCount n := by omega
  have hS_pos : 1 ≤ netEdgeCount n := by omega
  have h1_sq : 1 ≤ (netEdgeCount n) ^ 2 := Nat.one_le_pow 2 (netEdgeCount n) hS_pos
  have hn3_le_S3 : n ^ 3 ≤ (netEdgeCount n) ^ 3 := Nat.pow_le_pow_left hn_le_S 3
  have hd_6J : ∀ d ≤ 6 * paramJ n, d ^ 4 ≤ 63 ^ 4 * (netEdgeCount n) ^ 3 := fun d hd =>
    le_trans (Nat.pow_le_pow_left hd 4)
      (le_trans (le_of_lt (six_J_pow4_lt hn)) (Nat.mul_le_mul_left _ hn3_le_S3))
  have hsmall_size : ∀ c : QCSD_BoolCircuit, QCSD_circuitSize c ≤ 65 →
      QCSD_circuitSize c ≤ 500 * (netEdgeCount n) ^ 2 := fun c hc => by omega
  unfold expectedInc
  by_cases hv11 : v < netV11 n
  · rw [rawPred_of_V10 _ _ _ _ _ _ _ (by omega) hv11, (inOut_of_V10 (by omega) hv11).1, (inOut_of_V10 (by omega) hv11).2]
    dsimp only
    refine ⟨hsmall_size _ (by rw [constCircuit_size]; split_ifs <;> decide), hd_6J _ ?_⟩
    split_ifs
    · simp
    · simp; omega
  by_cases hv12 : v < netV12 n
  · rw [rawPred_of_V11 _ _ _ _ _ _ _ (by omega) hv12, (inOut_of_V11 (by omega) hv12).1, (inOut_of_V11 (by omega) hv12).2]
    have hovl_len : (ovlInLocal (paramJ n) (paramL n) (v - netV11 n)).length ≤ 2 := by
      unfold ovlInLocal; split_ifs <;> simp
    refine ⟨linearMapCheckCircuit_size_le_sq _ hS_pos (by omega) (by omega), hd_6J _ ?_⟩
    simp only [List.length_append, List.length_map, List.length_singleton]; omega
  by_cases hv13 : v < netV13 n
  · rw [rawPred_of_V12 _ _ _ _ _ _ _ (by omega) hv13, (inOut_of_V12 (by omega) hv13).1, (inOut_of_V12 (by omega) hv13).2]
    exact ⟨hsmall_size _ (le_trans (synCheckCircuit_wf_and_eval _ (fun _ => false)).2.2 (by decide)),
      hd_6J 3 (by omega)⟩
  by_cases hv14 : v < netV14 n
  · rw [rawPred_of_V13 _ _ _ _ _ _ _ (by omega) hv14, (inOut_of_V13 (by omega) hv14).1, (inOut_of_V13 (by omega) hv14).2]
    exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
  by_cases hv15 : v < netV15 n
  · rw [rawPred_of_V14 _ _ _ _ _ _ _ (by omega) hv15, (inOut_of_V14 (by omega) hv15).1, (inOut_of_V14 (by omega) hv15).2]
    exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
  by_cases hv16 : v < netV16 n
  · set tv := decodeTreeVert (treeLog n + 1) (v - netV15 n)
    have htv : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (tv.1, tv.2.1, tv.2.2) :=
      Prod.ext rfl (Prod.ext rfl rfl)
    rw [rawPred_of_V15 _ _ _ _ _ _ _ (by omega) hv16 htv,
        inEdges_of_V15 (by omega) hv16 htv, outEdges_of_V15 (by omega) hv16 htv]
    dsimp only
    by_cases hu0 : tv.2.2 = 0
    · simp only [hu0, ↓reduceIte]
      exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
    · simp only [hu0, ↓reduceIte]
      have hdeg5 : ((if tv.1 = 1 then
            [netE2 n + 2 * tv.2.1, netE2 n + 2 * tv.2.1 + 1,
             netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1)]
          else
            [netE12 n + treeEdgeOff (treeLog n + 1) (tv.1 - 1) + 2 * tv.2.1 * (2 * (tv.1 - 1) + 1) +
               sumWireLoc (tv.1 - 1) (tv.2.2 - 1),
             netE12 n + treeEdgeOff (treeLog n + 1) (tv.1 - 1) + (2 * tv.2.1 + 1) * (2 * (tv.1 - 1) + 1) +
               sumWireLoc (tv.1 - 1) (tv.2.2 - 1),
             netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1)]) ++
          [netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1) + 1,
           netE12 n + treeEdgeOff (treeLog n + 1) tv.1 + tv.2.1 * (2 * tv.1 + 1) + 2 * (tv.2.2 - 1) + 2]).length ≤
          6 * paramJ n := by
        split_ifs <;> simp <;> omega
      by_cases hsep : mode = 2 ∧ tv.1 = treeLog n + 1
      · rw [ite_pos hsep]
        exact ⟨hsmall_size _ (sepFullAdderCircuit_spec _ _ _ (fun _ => false)).2.2, hd_6J _ hdeg5⟩
      · rw [ite_neg hsep]
        exact ⟨hsmall_size _ (le_trans (fullAdderCircuit_wf_and_eval (fun _ => false)).2.2 (by decide)),
          hd_6J _ hdeg5⟩
  by_cases hv17 : v < netV17 n
  · rw [rawPred_of_V16 _ _ _ _ _ _ _ (by omega) hv17, (inOut_of_V16 (by omega) hv17).1, (inOut_of_V16 (by omega) hv17).2]
    exact ⟨hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide)), hd_6J 1 (by omega)⟩
  by_cases hv18 : v < netV18 n
  · rw [rawPred_of_V17 _ _ _ _ _ _ _ (by omega) hv18, (inOut_of_V17 (by omega) hv18).1, (inOut_of_V17 (by omega) hv18).2]
    dsimp only; refine ⟨?_, hd_6J 3 (by omega)⟩
    split_ifs
    · exact hsmall_size _ (le_trans (exactCmpStepCircuit_spec _ _ (fun _ => false)).2.2 (by decide))
    · exact hsmall_size _ (le_trans (borrowStepCircuit_wf_and_eval _ (fun _ => false)).2.2 (by decide))
    · exact hsmall_size _ (le_trans (sepCmpStepCircuit_spec (fun _ => false)).2.2 (by decide))
  rw [rawPred_of_V18 _ _ _ _ _ _ _ (by omega), (inOut_of_V18 (by omega)).1, (inOut_of_V18 (by omega)).2]
  refine ⟨?_, hd_6J 1 (by omega)⟩
  split_ifs
  · exact hsmall_size _ (by rw [constCircuit_size]; decide)
  · exact hsmall_size _ (le_trans (pinBitCircuit_size _) (by decide))

/-- Unified `QCSD_BoolTensorNetwork2` constructor across `Exact` (`0`), `Le` (`1`), and `Sep` (`2`). -/
def buildQCSDNet (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_BoolTensorNetwork2 :=
  ⟨netVertCount n,
   netEdgeCount n,
   netEnds n,
   netNoLoop n,
   fun v => rawPred mode n h s t0 t1 pre v.val,
   fun v => by
     rw [deg_netEnds]
     exact (rawPred_arity_and_wf mode n h s t0 t1 pre v.val v.isLt).1,
   fun v => (rawPred_arity_and_wf mode n h s t0 t1 pre v.val v.isLt).2⟩

lemma list_get_val_eq_getD {k : ℕ} {l1 : List (Fin k)} {l2 : List ℕ}
    (hb : ∀ x ∈ l2, x < k) (heq : l1 = listToFin l2 hb) (i : ℕ) (hi : i < l1.length) :
    (l1.get ⟨i, hi⟩).val = l2.getD i 0 := by
  subst heq
  exact listToFin_get_val l2 hb i hi

lemma vertexInp_buildQCSDNet (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (i : ℕ) (hi : i < (expectedInc n v.val).length) :
    vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x i =
      wireAt n x ((expectedInc n v.val).getD i 0) := by
  have hlen : i < (QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v).length := by
    rwa [deg_netEnds]
  unfold vertexInp
  change (if h_lt : i < (QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v).length
          then x ((QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v).get ⟨i, h_lt⟩)
          else false) = _
  rw [dite_pos hlen]
  set hbnd := (expectedInc_spec n v.val v.isLt).2.1
  have hget := list_get_val_eq_getD hbnd (incidentList_netEnds n v) i hlen
  have he_lt : (expectedInc n v.val).getD i 0 < netEdgeCount n := by
    rw [← hget]
    exact ((QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) v).get ⟨i, hlen⟩).isLt
  rw [wireAt_lt x he_lt]
  apply congrArg x
  exact Fin.ext hget

/-- Exact-weight QCSD Boolean tensor network `N_exact x pre` (§3.2, §4.1–§4.2, §5.1). -/
def N_exact (inp : QCSD_Instance) (pre : List Bool) : QCSD_BoolTensorNetwork2 :=
  buildQCSDNet 0 inp.n inp.h inp.s inp.t 0 pre

/-- At-most-`t` QCSD Boolean tensor network `N_le x pre` (§3.2, §4.1–§4.2, §5.1). -/
def N_le (inp : QCSD_Instance) (pre : List Bool) : QCSD_BoolTensorNetwork2 :=
  buildQCSDNet 1 inp.n inp.h inp.s inp.t 0 pre

/-- Split-weight QCSD Boolean tensor network `N_sep x pre` (§3.2, §4.1–§4.2, §5.1). -/
def N_sep (inp : QCSD_InstanceSep) (pre : List Bool) : QCSD_BoolTensorNetwork2 :=
  buildQCSDNet 2 inp.n inp.h inp.s inp.t₀ inp.t₁ pre

/-! ### Prefix Invariance, Linear Edge-Count Bounds, and `QCSD_TCClass2` Membership -/

theorem buildQCSDNet_prefix_invariant (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre1 pre2 : List Bool) :
    (buildQCSDNet mode n h s t0 t1 pre1).m = netVertCount n ∧
    (buildQCSDNet mode n h s t0 t1 pre1).k = netEdgeCount n ∧
    (buildQCSDNet mode n h s t0 t1 pre1).ends = netEnds n ∧
    QCSD_edgeCount2 (buildQCSDNet mode n h s t0 t1 pre1) =
      QCSD_edgeCount2 (buildQCSDNet mode n h s t0 t1 pre2) ∧
    QCSD_maxDeg2 (buildQCSDNet mode n h s t0 t1 pre1) =
      QCSD_maxDeg2 (buildQCSDNet mode n h s t0 t1 pre2) ∧
    (∀ v : Fin (netVertCount n), 2 * n ≤ v.val →
      (buildQCSDNet mode n h s t0 t1 pre1).pred v =
        (buildQCSDNet mode n h s t0 t1 pre2).pred v) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro v hv
  exact rawPred_pre_indep mode n h s t0 t1 pre1 pre2 hv

theorem N_exact_edgeCount_bounds (inp : QCSD_Instance) (pre : List Bool) (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (N_exact inp pre) ∧
    QCSD_edgeCount2 (N_exact inp pre) ≤ 420 * inp.n :=
  netEdgeCount_bounds hn

theorem N_le_edgeCount_bounds (inp : QCSD_Instance) (pre : List Bool) (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (N_le inp pre) ∧
    QCSD_edgeCount2 (N_le inp pre) ≤ 420 * inp.n :=
  netEdgeCount_bounds hn

theorem N_sep_edgeCount_bounds (inp : QCSD_InstanceSep) (pre : List Bool) (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (N_sep inp pre) ∧
    QCSD_edgeCount2 (N_sep inp pre) ≤ 420 * inp.n :=
  netEdgeCount_bounds hn

/-- Explicit `QCSD_TCClass2` constants shared uniformly across `N_exact`, `N_le`, and `N_sep`. -/
def tcCDelta : ℝ := 63
def tcKm : ℕ := 280
def tcKpred : ℕ := 500
def tcKcost : ℕ := 5 + 3 * tcKm + 9 * tcKm * (tcKpred + 1) ^ 2

theorem buildQCSDNet_tcClass2 {n : ℕ} (hn : 1 ≤ n)
    (mode : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_TCClass2 tcCDelta 1 tcKm 5 tcKcost 2 tcKpred
      (buildQCSDNet mode n h s t0 t1 pre) := by
  have hS_bounds := netEdgeCount_bounds hn
  have hS_eq : QCSD_edgeCount2 (buildQCSDNet mode n h s t0 t1 pre) = netEdgeCount n := rfl
  have hm_le : netVertCount n ≤ 280 * netEdgeCount n := by
    have hv := netVertCount_le hn
    have hn_le : n ≤ netEdgeCount n := by omega
    calc netVertCount n ≤ 280 * n := hv
         _ ≤ 280 * netEdgeCount n := Nat.mul_le_mul_left 280 hn_le
  apply tcClass2_of_bounds (buildQCSDNet mode n h s t0 t1 pre) tcKm tcKpred (by rw [hS_eq]; omega)
  · intro v
    change (QCSD_incidentList (netVertCount n) (netEdgeCount n) (netEnds n) ⟨v.val, v.isLt⟩).length ^ 4 ≤
      63 ^ 4 * (netEdgeCount n) ^ 3
    rw [deg_netEnds]
    exact (rawPred_size_and_deg hn mode h s t0 t1 pre v.val v.isLt).2
  · exact hm_le
  · intro v
    exact (rawPred_size_and_deg hn mode h s t0 t1 pre v.val v.isLt).1

theorem N_exact_tcClass2 (inp : QCSD_Instance) (pre : List Bool) (hn : 1 ≤ inp.n) :
    QCSD_TCClass2 tcCDelta 1 tcKm 5 tcKcost 2 tcKpred (N_exact inp pre) :=
  buildQCSDNet_tcClass2 hn 0 inp.h inp.s inp.t 0 pre

theorem N_le_tcClass2 (inp : QCSD_Instance) (pre : List Bool) (hn : 1 ≤ inp.n) :
    QCSD_TCClass2 tcCDelta 1 tcKm 5 tcKcost 2 tcKpred (N_le inp pre) :=
  buildQCSDNet_tcClass2 hn 1 inp.h inp.s inp.t 0 pre

theorem N_sep_tcClass2 (inp : QCSD_InstanceSep) (pre : List Bool) (hn : 1 ≤ inp.n) :
    QCSD_TCClass2 tcCDelta 1 tcKm 5 tcKcost 2 tcKpred (N_sep inp pre) :=
  buildQCSDNet_tcClass2 hn 2 inp.h inp.s inp.t₀ inp.t₁ pre

/-!
## Part 5: Solution-Count Preservation (`QCSD_contraction2`) & Witness Decoding (`QCSD_decodeSolPair`)
-/

/-- Canonical `2 * n`-bit interface representation of a candidate error pair `(e₀, e₁)`. -/
def QCSD_iface (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) : List Bool :=
  QCSD_vecToBits e₀ ++ QCSD_vecToBits e₁

lemma getD_eq_getElem_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma list_getD_append_right (l1 l2 : List Bool) (i : ℕ) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma vecToBits_length {n : ℕ} (v : Fin n → ZMod 2) : (QCSD_vecToBits v).length = n := by
  simp [QCSD_vecToBits]

lemma vecToBits_getD {n : ℕ} (v : Fin n → ZMod 2) {i : ℕ} (hi : i < n) :
    (QCSD_vecToBits v).getD i false = zmod2ToBool (v ⟨i, hi⟩) := by
  unfold QCSD_vecToBits zmod2ToBool
  have hlen : i < ((List.finRange n).map (fun j : Fin n => decide (v j = (1 : ZMod 2)))).length := by
    simp [hi]
  rw [getD_eq_getElem_of_lt _ _ hlen, List.getElem_map, List.getElem_finRange]
  rfl

lemma iface_length (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) :
    (QCSD_iface n e₀ e₁).length = 2 * n := by
  simp only [QCSD_iface, List.length_append, vecToBits_length]
  omega

lemma iface_getD_left {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) {i : ℕ} (hi : i < n) :
    (QCSD_iface n e₀ e₁).getD i false = zmod2ToBool (e₀ ⟨i, hi⟩) := by
  unfold QCSD_iface
  rw [list_getD_append_left _ _ _ (by rw [vecToBits_length]; exact hi), vecToBits_getD e₀ hi]

lemma iface_getD_right {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) {i : ℕ} (hi : i < n) :
    (QCSD_iface n e₀ e₁).getD (n + i) false = zmod2ToBool (e₁ ⟨i, hi⟩) := by
  unfold QCSD_iface
  rw [list_getD_append_right _ _ _ (by rw [vecToBits_length]; omega),
      vecToBits_length, Nat.add_sub_cancel_left, vecToBits_getD e₁ hi]

theorem decodeSolPair_iface (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) :
    QCSD_decodeSolPair n (QCSD_iface n e₀ e₁) = some (e₀, e₁) := by
  unfold QCSD_decodeSolPair
  rw [ite_pos (iface_length n e₀ e₁)]
  congr 1
  apply Prod.ext <;> funext i <;> dsimp only
  · rw [iface_getD_left e₀ e₁ i.isLt]
    exact boolToZMod2_zmod2ToBool (e₀ i)
  · rw [iface_getD_right e₀ e₁ i.isLt]
    exact boolToZMod2_zmod2ToBool (e₁ i)

theorem iface_of_decodeSolPair {n : ℕ} {w : List Bool} {e₀ e₁ : Fin n → ZMod 2}
    (h : QCSD_decodeSolPair n w = some (e₀, e₁)) :
    QCSD_iface n e₀ e₁ = w := by
  unfold QCSD_decodeSolPair at h
  split_ifs at h with hlen
  injection h with hp
  obtain ⟨he0, he1⟩ := Prod.mk.inj hp
  apply List.ext_getElem ((iface_length n e₀ e₁).trans hlen.symm)
  intro k hk1 hk2
  rw [← getD_eq_getElem_of_lt _ false hk1, ← getD_eq_getElem_of_lt _ false hk2]
  by_cases hkn : k < n
  · rw [iface_getD_left e₀ e₁ hkn, ← he0]
    exact zmod2ToBool_boolToZMod2 (w.getD k false)
  · have hsub : k - n < n := by omega
    have hk_eq : n + (k - n) = k := by omega
    conv_lhs => rw [← hk_eq]
    rw [iface_getD_right e₀ e₁ hsub, ← he1]
    dsimp only
    rw [hk_eq]
    exact zmod2ToBool_boolToZMod2 (w.getD k false)

theorem iface_eq_iff_decodeSolPair {n : ℕ} {w : List Bool} (e₀ e₁ : Fin n → ZMod 2) :
    QCSD_iface n e₀ e₁ = w ↔ QCSD_decodeSolPair n w = some (e₀, e₁) :=
  ⟨fun h => h ▸ decodeSolPair_iface n e₀ e₁, iface_of_decodeSolPair⟩

def ifaceVec (n : ℕ) (p : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : Fin (2 * n) → Bool :=
  fun k => if hk : k.val < n then zmod2ToBool (p.1 ⟨k.val, hk⟩)
           else zmod2ToBool (p.2 ⟨k.val - n, by omega⟩)

def decodeIfaceVec (n : ℕ) (w : Fin (2 * n) → Bool) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun i => boolToZMod2 (w ⟨i.val, by omega⟩),
   fun i => boolToZMod2 (w ⟨n + i.val, by omega⟩))

lemma decodeIfaceVec_ifaceVec (n : ℕ) (p : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    decodeIfaceVec n (ifaceVec n p) = p := by
  rcases p with ⟨e₀, e₁⟩
  apply Prod.ext <;> funext i <;> unfold decodeIfaceVec ifaceVec <;> dsimp only
  · split_ifs with hk
    · exact boolToZMod2_zmod2ToBool (e₀ i)
    · exact absurd i.isLt hk
  · split_ifs with hk
    · omega
    · have hsub : (⟨n + i.val - n, by omega⟩ : Fin n) = i := by apply Fin.ext; dsimp only; omega
      rw [hsub]
      exact boolToZMod2_zmod2ToBool (e₁ i)

lemma ifaceVec_decodeIfaceVec (n : ℕ) (w : Fin (2 * n) → Bool) :
    ifaceVec n (decodeIfaceVec n w) = w := by
  funext k
  unfold ifaceVec decodeIfaceVec
  dsimp only
  split_ifs with hk
  · exact zmod2ToBool_boolToZMod2 (w k)
  · rw [zmod2ToBool_boolToZMod2]
    apply congrArg w
    apply Fin.ext; dsimp only; omega

lemma iface_getD_eq_ifaceVec {n : ℕ} (p : (Fin n → ZMod 2) × (Fin n → ZMod 2))
    (k : Fin (2 * n)) :
    (QCSD_iface n p.1 p.2).getD k.val false = ifaceVec n p k := by
  unfold ifaceVec
  split_ifs with hk
  · exact iface_getD_left p.1 p.2 hk
  · have hsub : k.val - n < n := by omega
    have heq : k.val = n + (k.val - n) := by omega
    conv_lhs => rw [heq]
    exact iface_getD_right p.1 p.2 hsub

lemma iface_take_eq_iff {n : ℕ} (p : (Fin n → ZMod 2) × (Fin n → ZMod 2))
    {pre : List Bool} (hpre : pre.length ≤ 2 * n) :
    (QCSD_iface n p.1 p.2).take pre.length = pre ↔
      ∀ i : Fin (2 * n), i.val < pre.length → ifaceVec n p i = pre.getD i.val false := by
  have hlen_if : (QCSD_iface n p.1 p.2).length = 2 * n := iface_length n p.1 p.2
  have hlen_tk : ((QCSD_iface n p.1 p.2).take pre.length).length = pre.length := by
    simp [hlen_if, hpre]
  constructor
  · intro htk i hi
    have hi_tk : i.val < ((QCSD_iface n p.1 p.2).take pre.length).length := by omega
    have h1 : ((QCSD_iface n p.1 p.2).take pre.length)[i.val] = pre[i.val] := by simp [htk]
    rw [List.getElem_take, ← getD_eq_getElem_of_lt _ false (by omega),
        ← getD_eq_getElem_of_lt _ false hi, iface_getD_eq_ifaceVec p i] at h1
    exact h1
  · intro hall
    apply List.ext_getElem hlen_tk
    intro k hk1 hk2
    rw [List.getElem_take, ← getD_eq_getElem_of_lt _ false (by omega),
        ← getD_eq_getElem_of_lt _ false hk2]
    have hk_2n : k < 2 * n := by omega
    rw [iface_getD_eq_ifaceVec p ⟨k, hk_2n⟩]
    exact hall ⟨k, hk_2n⟩ hk2

/-! ### Adder-Tree Subtree Weight Lemmas (`padLeaves` ↔ `QCSD_wt`) -/

def padLeaves (n : ℕ) (w : Fin (2 * n) → Bool) (leaf : ℕ) : Bool :=
  if h0 : leaf < n then w ⟨leaf, by omega⟩
  else if h0' : leaf < treeM n then false
  else if h1 : leaf < treeM n + n then w ⟨n + (leaf - treeM n), by omega⟩
  else false

lemma treeLevelBits_congr_sub {N1 N2 : ℕ} {f g : ℕ → Bool} :
    ∀ (j node1 node2 : ℕ),
      (∀ t < 2 ^ j,
        (decide (node1 * 2 ^ j + t < N1) && f (node1 * 2 ^ j + t)) =
          (decide (node2 * 2 ^ j + t < N2) && g (node2 * 2 ^ j + t))) →
      treeLevelBits N1 f j node1 = treeLevelBits N2 g j node2
  | 0, node1, node2, h => by
    funext b
    simp only [treeLevelBits]
    by_cases hb0 : b = 0
    · subst hb0
      have h0 := h 0 (by decide)
      simpa using h0
    · simp [hb0]
  | j + 1, node1, node2, h => by
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    have hL : treeLevelBits N1 f j (2 * node1) = treeLevelBits N2 g j (2 * node2) := by
      apply treeLevelBits_congr_sub j (2 * node1) (2 * node2)
      intro t ht
      have heq1 : (2 * node1) * 2 ^ j + t = node1 * 2 ^ (j + 1) + t := by rw [hpow]; ring
      have heq2 : (2 * node2) * 2 ^ j + t = node2 * 2 ^ (j + 1) + t := by rw [hpow]; ring
      rw [heq1, heq2]
      exact h t (by omega)
    have hR : treeLevelBits N1 f j (2 * node1 + 1) = treeLevelBits N2 g j (2 * node2 + 1) := by
      apply treeLevelBits_congr_sub j (2 * node1 + 1) (2 * node2 + 1)
      intro t ht
      have heq1 : (2 * node1 + 1) * 2 ^ j + t = node1 * 2 ^ (j + 1) + (2 ^ j + t) := by rw [hpow]; ring
      have heq2 : (2 * node2 + 1) * 2 ^ j + t = node2 * 2 ^ (j + 1) + (2 ^ j + t) := by rw [hpow]; ring
      rw [heq1, heq2]
      exact h (2 ^ j + t) (by omega)
    funext b
    simp only [treeLevelBits, hL, hR]

lemma sum_fin_eq_sum_range (n : ℕ) (g : ℕ → ℕ) :
    Finset.sum Finset.univ (fun i : Fin n => g i.val) = Finset.sum (Finset.range n) g := by
  apply Finset.sum_bij (fun (i : Fin n) _ => i.val)
  · intro i _; exact Finset.mem_range.mpr i.isLt
  · intro _ _ _ _ h; exact Fin.ext h
  · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

lemma wt_boolToZMod2 {n : ℕ} (u : ℕ → Bool) :
    QCSD_wt (fun i : Fin n => boolToZMod2 (u i.val)) =
      Finset.sum (Finset.range n) (fun i => if u i then 1 else 0) := by
  unfold QCSD_wt hammingNorm
  rw [Finset.card_filter]
  have h1 : (fun i : Fin n => if boolToZMod2 (u i.val) ≠ 0 then (1 : ℕ) else 0) =
      (fun i : Fin n => if u i.val then 1 else 0) := by
    funext i
    cases u i.val <;> decide
  rw [h1]
  exact sum_fin_eq_sum_range n (fun k => if u k then 1 else 0)

lemma padLeaves_wt0 (n : ℕ) (w : Fin (2 * n) → Bool) :
    bitsVal (treeLog n + 1) (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 0) =
      QCSD_wt (decodeIfaceVec n w).1 := by
  let g : ℕ → Bool := fun i => if hi : i < n then w ⟨i, by omega⟩ else false
  have hsub : treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 0 =
      treeLevelBits n g (treeLog n) 0 := by
    apply treeLevelBits_congr_sub (treeLog n) 0 0
    intro t ht
    have ht_M : t < treeM n := ht
    have ht_2M : t < 2 * treeM n := by omega
    simp only [Nat.zero_mul, Nat.zero_add, ht_2M, decide_true, Bool.true_and]
    unfold padLeaves
    by_cases htn : t < n
    · simp [htn, g]
    · simp [htn, ht_M]
  rw [hsub, treeTop_val_eq_sum n g]
  have hd : (decodeIfaceVec n w).1 = (fun i : Fin n => boolToZMod2 (g i.val)) := by
    funext i; simp [decodeIfaceVec, g, i.isLt]
  rw [hd, wt_boolToZMod2 g]

lemma padLeaves_wt1 (n : ℕ) (w : Fin (2 * n) → Bool) :
    bitsVal (treeLog n + 1) (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 1) =
      QCSD_wt (decodeIfaceVec n w).2 := by
  let g : ℕ → Bool := fun i => if hi : i < n then w ⟨n + i, by omega⟩ else false
  have hM1 : n ≤ treeM n := le_treeM n
  have hsub : treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 1 =
      treeLevelBits n g (treeLog n) 0 := by
    apply treeLevelBits_congr_sub (treeLog n) 1 0
    intro t ht
    have ht_M : t < treeM n := ht
    have hpow : 1 * 2 ^ treeLog n + t = treeM n + t := by unfold treeM; omega
    have hlt_2M : treeM n + t < 2 * treeM n := by omega
    rw [hpow]
    simp only [Nat.zero_mul, Nat.zero_add, hlt_2M, decide_true, Bool.true_and]
    unfold padLeaves
    have hn1 : ¬(treeM n + t < n) := by omega
    have hn2 : ¬(treeM n + t < treeM n) := by omega
    by_cases htn : t < n
    · have hy : treeM n + t < treeM n + n := by omega
      simp only [hn1, hn2, hy, htn, ↓reduceDIte, decide_true, Bool.true_and, g]
      apply congrArg w; apply Fin.ext; dsimp only; omega
    · have hny : ¬(treeM n + t < treeM n + n) := by omega
      simp [hn1, hn2, hny, htn]
  rw [hsub, treeTop_val_eq_sum n g]
  have hd : (decodeIfaceVec n w).2 = (fun i : Fin n => boolToZMod2 (g i.val)) := by
    funext i; simp [decodeIfaceVec, g, i.isLt]
  rw [hd, wt_boolToZMod2 g]

lemma padLeaves_wt_sum (n : ℕ) (w : Fin (2 * n) → Bool) :
    bitsVal (treeLog n + 2) (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n + 1) 0) =
      QCSD_wt (decodeIfaceVec n w).1 + QCSD_wt (decodeIfaceVec n w).2 := by
  change bitsVal ((treeLog n + 1) + 1)
    (rippleSum (treeLog n + 1)
      (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 0)
      (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 1)) = _
  rw [rippleSum_val, padLeaves_wt0, padLeaves_wt1]

/-! ### Canonical Wire Assignment `extWire` & Block Selectors -/

def hBit (n : ℕ) (h : Fin n → ZMod 2) (idx : ℕ) : Bool :=
  if hlt : idx < n then zmod2ToBool (h ⟨idx, hlt⟩) else false

def e1Bit (n : ℕ) (w : Fin (2 * n) → Bool) (idx : ℕ) : Bool :=
  if hlt : idx < n then w ⟨n + idx, by omega⟩ else false

def mulWiresYa (n : ℕ) (h : Fin n → ZMod 2) : ℕ → ℕ → ℕ → Bool :=
  twoLayerFwdSt1 n (hBit n h)

def mulWiresFa (n : ℕ) (h : Fin n → ZMod 2) : ℕ → ℕ → Bool :=
  twoLayerFwdSt2 n (mulWiresYa n h)

def mulWiresYb (n : ℕ) (w : Fin (2 * n) → Bool) : ℕ → ℕ → ℕ → Bool :=
  twoLayerFwdSt1 n (e1Bit n w)

def mulWiresFb (n : ℕ) (w : Fin (2 * n) → Bool) : ℕ → ℕ → Bool :=
  twoLayerFwdSt2 n (mulWiresYb n w)

def mulWiresFc (n : ℕ) (h : Fin n → ZMod 2) (w : Fin (2 * n) → Bool) (q p : ℕ) : Bool :=
  ringMulBits (paramJ n) (mulWiresFa n h q) (mulWiresFb n w q) p

def mulWiresYc (n : ℕ) (h : Fin n → ZMod 2) (w : Fin (2 * n) → Bool) : ℕ → ℕ → ℕ → Bool :=
  twoLayerInvSt1 n (mulWiresFc n h w)

def mulWiresCraw (n : ℕ) (h : Fin n → ZMod 2) (w : Fin (2 * n) → Bool) : ℕ → ℕ → Bool :=
  twoLayerInvSt2 n (mulWiresYc n h w)

def mulWiresZ (n : ℕ) (h : Fin n → ZMod 2) (w : Fin (2 * n) → Bool) (k : ℕ) : Bool :=
  twoLayerPolyMulBit n (hBit n h) (e1Bit n w) k

def treeWireVal (n : ℕ) (w : Fin (2 * n) → Bool) (locE : ℕ) : Bool :=
  let r := treeLog n + 1
  let te := decodeTreeEdge r locE
  let j := te.1; let node := te.2.1; let wi := te.2.2
  if wi % 2 = 0 ∧ wi < 2 * j then
    rippleCarry (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node))
                (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node + 1)) (wi / 2)
  else
    let bitIdx := if wi = 2 * j then j else wi / 2
    treeLevelBits (2 * treeM n) (padLeaves n w) j node bitIdx

def borrowWireVal (mode n t0 : ℕ) (w : Fin (2 * n) → Bool) (b : ℕ) : Bool :=
  if mode = 1 then
    leBorrow (treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n + 1) 0) t0 b
  else false

def rawExtWire (mode n : ℕ) (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool) (e : ℕ) : Bool :=
  let J := paramJ n
  let L1 := paramL1 n
  if h1 : e < netE1 n then w ⟨e, h1⟩
  else if h2 : e < netE2 n then w ⟨e - netE1 n, by have : netE2 n = 4 * n := rfl; change e - 2 * n < 2 * n; omega⟩
  else if e < netE3 n then padLeaves n w (e - netE2 n)
  else if e < netE4 n then hBit n h (e - netE3 n)
  else if e < netE5 n then
    let idx := e - netE4 n
    let q := idx / (2 * J)
    mulWiresYa n h (q / L1) (q % L1) (idx % (2 * J))
  else if e < netE6 n then
    let idx := e - netE5 n
    mulWiresFa n h (idx / (2 * J)) (idx % (2 * J))
  else if e < netE7 n then
    let idx := e - netE6 n
    let q := idx / (2 * J)
    mulWiresYb n w (q / L1) (q % L1) (idx % (2 * J))
  else if e < netE8 n then
    let idx := e - netE7 n
    mulWiresFb n w (idx / (2 * J)) (idx % (2 * J))
  else if e < netE9 n then
    let idx := e - netE8 n
    mulWiresFc n h w (idx / (2 * J)) (idx % (2 * J))
  else if e < netE10 n then
    let idx := e - netE9 n
    let q := idx / (2 * J)
    mulWiresYc n h w (q / L1) (q % L1) (idx % (2 * J))
  else if e < netE11 n then
    let idx := e - netE10 n
    mulWiresCraw n h w (idx / (2 * J)) (idx % (2 * J))
  else if e < netE12 n then
    mulWiresZ n h w (e - netE11 n)
  else if e < netE13 n then
    treeWireVal n w (e - netE12 n)
  else
    borrowWireVal mode n t0 w (e - netE13 n)

def extWire (mode n : ℕ) (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool) :
    Fin (netEdgeCount n) → Bool :=
  fun e => rawExtWire mode n h t0 w e.val

lemma wireAt_extWire {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (he : e < netEdgeCount n) :
    wireAt n (extWire mode n h t0 w) e = rawExtWire mode n h t0 w e :=
  wireAt_lt _ he

lemma netE1_le_netEdgeCount (n : ℕ) : 2 * n ≤ netEdgeCount n := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, h1213, h13_lt⟩
  change netE1 n ≤ netEdgeCount n
  omega

lemma extWire_iface (mode n : ℕ) (h : Fin n → ZMod 2) (t0 : ℕ)
    (w : Fin (2 * n) → Bool) (i : Fin (2 * n)) :
    extWire mode n h t0 w ⟨i.val, lt_of_lt_of_le i.isLt (netE1_le_netEdgeCount n)⟩ = w i := by
  unfold extWire rawExtWire
  dsimp only
  simp only [show i.val < netE1 n from i.isLt, ↓reduceDIte]

lemma rawExtWire_of_B0 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hhi : e < netE1 n) :
    rawExtWire mode n h t0 w e = w ⟨e, hhi⟩ := by
  unfold rawExtWire; dsimp only; simp only [hhi, ↓reduceDIte]

lemma rawExtWire_of_B1 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE1 n ≤ e) (hhi : e < netE2 n) :
    rawExtWire mode n h t0 w e =
      w ⟨e - netE1 n, by have : netE2 n = 4 * n := rfl; change e - 2 * n < 2 * n; omega⟩ := by
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, hhi, ↓reduceDIte]

lemma rawExtWire_of_B2 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE2 n ≤ e) (hhi : e < netE3 n) :
    rawExtWire mode n h t0 w e = padLeaves n w (e - netE2 n) := by
  rcases netE_chain n with ⟨_, h12, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B3 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE3 n ≤ e) (hhi : e < netE4 n) :
    rawExtWire mode n h t0 w e = hBit n h (e - netE3 n) := by
  rcases netE_chain n with ⟨_, h12, h23, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B4 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE4 n ≤ e) (hhi : e < netE5 n) :
    rawExtWire mode n h t0 w e =
      mulWiresYa n h (((e - netE4 n) / (2 * paramJ n)) / paramL1 n)
        (((e - netE4 n) / (2 * paramJ n)) % paramL1 n) ((e - netE4 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B5 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE5 n ≤ e) (hhi : e < netE6 n) :
    rawExtWire mode n h t0 w e =
      mulWiresFa n h ((e - netE5 n) / (2 * paramJ n)) ((e - netE5 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B6 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE6 n ≤ e) (hhi : e < netE7 n) :
    rawExtWire mode n h t0 w e =
      mulWiresYb n w (((e - netE6 n) / (2 * paramJ n)) / paramL1 n)
        (((e - netE6 n) / (2 * paramJ n)) % paramL1 n) ((e - netE6 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B7 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE7 n ≤ e) (hhi : e < netE8 n) :
    rawExtWire mode n h t0 w e =
      mulWiresFb n w ((e - netE7 n) / (2 * paramJ n)) ((e - netE7 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B8 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE8 n ≤ e) (hhi : e < netE9 n) :
    rawExtWire mode n h t0 w e =
      mulWiresFc n h w ((e - netE8 n) / (2 * paramJ n)) ((e - netE8 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B9 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE9 n ≤ e) (hhi : e < netE10 n) :
    rawExtWire mode n h t0 w e =
      mulWiresYc n h w (((e - netE9 n) / (2 * paramJ n)) / paramL1 n)
        (((e - netE9 n) / (2 * paramJ n)) % paramL1 n) ((e - netE9 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega,
             show ¬(e < netE9 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B10 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE10 n ≤ e) (hhi : e < netE11 n) :
    rawExtWire mode n h t0 w e =
      mulWiresCraw n h w ((e - netE10 n) / (2 * paramJ n)) ((e - netE10 n) % (2 * paramJ n)) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega,
             show ¬(e < netE9 n) by omega, show ¬(e < netE10 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B11 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE11 n ≤ e) (hhi : e < netE12 n) :
    rawExtWire mode n h t0 w e = mulWiresZ n h w (e - netE11 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega,
             show ¬(e < netE9 n) by omega, show ¬(e < netE10 n) by omega,
             show ¬(e < netE11 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B12 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE12 n ≤ e) (hhi : e < netE13 n) :
    rawExtWire mode n h t0 w e = treeWireVal n w (e - netE12 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega,
             show ¬(e < netE9 n) by omega, show ¬(e < netE10 n) by omega,
             show ¬(e < netE11 n) by omega, show ¬(e < netE12 n) by omega, hhi, ↓reduceDIte, ↓reduceIte]

lemma rawExtWire_of_B13 {mode n : ℕ} (h : Fin n → ZMod 2) (t0 : ℕ) (w : Fin (2 * n) → Bool)
    {e : ℕ} (hlo : netE13 n ≤ e) :
    rawExtWire mode n h t0 w e = borrowWireVal mode n t0 w (e - netE13 n) := by
  rcases netE_chain n with ⟨_, h12, h23, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, h1213, _⟩
  unfold rawExtWire; dsimp only
  simp only [show ¬(e < netE1 n) by omega, show ¬(e < netE2 n) by omega,
             show ¬(e < netE3 n) by omega, show ¬(e < netE4 n) by omega,
             show ¬(e < netE5 n) by omega, show ¬(e < netE6 n) by omega,
             show ¬(e < netE7 n) by omega, show ¬(e < netE8 n) by omega,
             show ¬(e < netE9 n) by omega, show ¬(e < netE10 n) by omega,
             show ¬(e < netE11 n) by omega, show ¬(e < netE12 n) by omega,
             show ¬(e < netE13 n) by omega, ↓reduceDIte, ↓reduceIte]

/-! ### `List.getD` & Per-Vertex `vertexSat` Characterizations (`V0..V18`) -/

lemma getD_append_left_nat (l1 l2 : List ℕ) {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  rw [getD_eq_getElem_of_lt _ _ (by simp; omega), getD_eq_getElem_of_lt _ _ hi,
      List.getElem_append_left hi]

lemma getD_append_add_nat (l1 l2 : List ℕ) {j : ℕ} (hj : j < l2.length) :
    (l1 ++ l2).getD (l1.length + j) 0 = l2.getD j 0 := by
  rw [getD_eq_getElem_of_lt _ _ (by simp [hj]), getD_eq_getElem_of_lt _ _ hj,
      List.getElem_append_right (Nat.le_add_right _ _)]
  simp

lemma getD_map_nat (l : List ℕ) (f : ℕ → ℕ) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [getD_eq_getElem_of_lt _ _ (by simp [hi]), getD_eq_getElem_of_lt _ _ hi, List.getElem_map]

lemma getD_range_nat {m i : ℕ} (hi : i < m) : (List.range m).getD i 0 = i := by
  rw [getD_eq_getElem_of_lt _ _ (by simp [hi]), List.getElem_range]

lemma getD_range_map_nat {m i : ℕ} (f : ℕ → ℕ) (hi : i < m) :
    ((List.range m).map f).getD i 0 = f i := by
  rw [getD_map_nat _ f (by simp [hi]), getD_range_nat hi]

lemma foldl_bne_congr {B : ℕ} {f1 f2 : ℕ → Bool} (hf : ∀ i < B, f1 i = f2 i) :
    ∀ (l : List ℕ) (init : Bool), (∀ i ∈ l, i < B) →
      l.foldl (fun b i => bne b (f1 i)) init = l.foldl (fun b i => bne b (f2 i)) init
  | [], _, _ => rfl
  | a :: as, init, hl => by
    simp only [List.foldl_cons]
    rw [hf a (hl a (by simp))]
    exact foldl_bne_congr hf as _ (fun x hx => hl x (List.mem_cons_of_mem a hx))

lemma linearMapTarget_congr {numIn : ℕ} (mat : ℕ → ℕ → Bool) {inp1 inp2 : ℕ → Bool}
    (h : ∀ i < numIn, inp1 i = inp2 i) (j : ℕ) :
    linearMapTarget numIn mat inp1 j = linearMapTarget numIn mat inp2 j := by
  unfold linearMapTarget
  exact foldl_bne_congr h _ false (fun i hi => List.mem_range.mp (List.mem_of_mem_filter hi))

lemma bilinearMapTarget_congr {n1 n2 : ℕ} (hn2 : 0 < n2) (tensor : ℕ → ℕ → ℕ → Bool)
    {inp1 inp2 : ℕ → Bool} (h : ∀ i < n1 + n2, inp1 i = inp2 i) (j : ℕ) :
    bilinearMapTarget n1 n2 tensor inp1 j = bilinearMapTarget n1 n2 tensor inp2 j := by
  unfold bilinearMapTarget
  apply foldl_bne_congr (B := n1 * n2)
  · intro k hk
    have hdiv : k / n2 < n1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk)
    have hmod : k % n2 < n2 := Nat.mod_lt k hn2
    rw [h (k / n2) (by omega), h (n1 + k % n2) (by omega)]
  · intro k hk
    exact List.mem_range.mp (List.mem_of_mem_filter hk)

/-- Generic evaluator for any `linearMapCheckCircuit` vertex in `buildQCSDNet`. -/
lemma eval_linear_vertex (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (inL outL : List ℕ) (mat : ℕ → ℕ → Bool)
    (hpred : rawPred mode n h s t0 t1 pre v.val = linearMapCheckCircuit inL.length outL.length mat)
    (hin : inEdges n v.val = inL) (hout : outEdges n v.val = outL) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      ∀ k < outL.length,
        wireAt n x (outL.getD k 0) =
          linearMapTarget inL.length mat (fun i => wireAt n x (inL.getD i 0)) k := by
  have hexp : expectedInc n v.val = inL ++ outL := by unfold expectedInc; rw [hin, hout]
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
    (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) = true ↔ _
  rw [hpred, (linearMapCheckCircuit_spec inL.length outL.length mat _).2.1, List.all_eq_true]
  constructor
  · intro hall k hk
    have hstep := hall k (List.mem_range.mpr hk)
    rw [beq_iff_eq] at hstep
    have hout_val : vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x (inL.length + k) =
        wireAt n x (outL.getD k 0) := by
      rw [vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x _ (by rw [hexp]; simp [hk])]
      rw [hexp, getD_append_add_nat inL outL hk]
    have hin_congr : linearMapTarget inL.length mat
        (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) k =
        linearMapTarget inL.length mat (fun i => wireAt n x (inL.getD i 0)) k := by
      apply linearMapTarget_congr
      intro i hi
      rw [vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x i (by rw [hexp]; simp; omega)]
      rw [hexp, getD_append_left_nat inL outL hi]
    rw [← hout_val, ← hin_congr]
    exact hstep
  · intro hall k hk
    have hk' : k < outL.length := List.mem_range.mp hk
    rw [beq_iff_eq]
    rw [vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x (inL.length + k) (by rw [hexp]; simp [hk']),
        hexp, getD_append_add_nat inL outL hk']
    have hin_congr : linearMapTarget inL.length mat
        (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) k =
        linearMapTarget inL.length mat (fun i => wireAt n x (inL.getD i 0)) k := by
      apply linearMapTarget_congr
      intro i hi
      rw [vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x i (by rw [hexp]; simp; omega),
          hexp, getD_append_left_nat inL outL hi]
    rw [hin_congr]
    exact hall k hk'

/-- Generic evaluator for 1-edge `pinBitCircuit` vertices in `buildQCSDNet`. -/
lemma eval_pin_vertex (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (e : ℕ) (opt : Option Bool)
    (hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit opt)
    (hexp : expectedInc n v.val = [e]) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      match opt with
      | none => True
      | some b => wireAt n x e = b := by
  have h_eval : vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x =
      QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
        (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) := rfl
  cases opt with
  | none =>
    simp only [h_eval, hpred, pinBitCircuit_eval]
  | some b =>
    dsimp only
    rw [h_eval, hpred, pinBitCircuit_eval,
        vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 0 (by rw [hexp]; simp),
        hexp, List.getD_cons_zero, beq_iff_eq]

lemma eval_V7 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (hlo : netV7 n ≤ v.val) (hhi : v.val < netV8 n) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      ∀ p < 2 * paramJ n,
        wireAt n x (netE8 n + (v.val - netV7 n) * (2 * paramJ n) + p) =
          ringMulBits (paramJ n)
            (fun m => wireAt n x (netE5 n + (v.val - netV7 n) * (2 * paramJ n) + m))
            (fun m => wireAt n x (netE7 n + (v.val - netV7 n) * (2 * paramJ n) + m)) p := by
  have h2J : 0 < 2 * paramJ n := by have := paramJ_pos n; omega
  set q := v.val - netV7 n
  set inL := (List.range (2 * paramJ n)).map (fun p => netE5 n + q * (2 * paramJ n) + p) ++
             (List.range (2 * paramJ n)).map (fun p => netE7 n + q * (2 * paramJ n) + p)
  set outL := (List.range (2 * paramJ n)).map (fun p => netE8 n + q * (2 * paramJ n) + p)
  have hexp : expectedInc n v.val = inL ++ outL := by
    unfold expectedInc
    rw [(inOut_of_V7 hlo hhi).1, (inOut_of_V7 hlo hhi).2]
  have hin_len : inL.length = 2 * paramJ n + 2 * paramJ n := by simp [inL]
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
    (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) = true ↔ _
  rw [rawPred_of_V7 mode n h s t0 t1 pre hlo hhi,
      (bilinearMapCheckCircuit_spec (2 * paramJ n) (2 * paramJ n) (2 * paramJ n)
        (ringMulTensor (paramJ n)) h2J _).2.1,
      List.all_eq_true]
  have hin_congr : ∀ p,
      bilinearMapTarget (2 * paramJ n) (2 * paramJ n) (ringMulTensor (paramJ n))
        (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) p =
      ringMulBits (paramJ n)
        (fun m => wireAt n x (netE5 n + q * (2 * paramJ n) + m))
        (fun m => wireAt n x (netE7 n + q * (2 * paramJ n) + m)) p := by
    intro p
    unfold ringMulBits
    apply bilinearMapTarget_congr h2J
    intro i hi
    rw [vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x i (by rw [hexp]; simp [inL, outL]; omega),
        hexp, getD_append_left_nat inL outL (by omega)]
    by_cases hi1 : i < 2 * paramJ n
    · simp only [hi1, ↓reduceIte, inL]
      rw [getD_append_left_nat _ _ (by simp [hi1]), getD_range_map_nat _ hi1]
    · simp only [hi1, ↓reduceIte, inL]
      have hsub : i - 2 * paramJ n < 2 * paramJ n := by omega
      have hi_eq : i = ((List.range (2 * paramJ n)).map
          (fun m => netE5 n + q * (2 * paramJ n) + m)).length + (i - 2 * paramJ n) := by
        simp; omega
      conv_lhs => rw [hi_eq]
      rw [getD_append_add_nat _ _ (by simp [hsub]), getD_range_map_nat _ hsub]
  constructor
  · intro hall p hp
    have hstep := hall p (List.mem_range.mpr hp)
    rw [beq_iff_eq, hin_congr p] at hstep
    rw [← hin_len,
        vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x (inL.length + p) (by rw [hexp]; simp [outL, hp]),
        hexp, getD_append_add_nat inL outL (by simp [outL, hp]),
        getD_range_map_nat _ hp] at hstep
    exact hstep
  · intro hall p hp
    have hp' : p < 2 * paramJ n := List.mem_range.mp hp
    rw [beq_iff_eq, hin_congr p, ← hin_len,
        vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x (inL.length + p) (by rw [hexp]; simp [outL, hp']),
        hexp, getD_append_add_nat inL outL (by simp [outL, hp']),
        getD_range_map_nat _ hp']
    exact hall p hp'

lemma eval_V10 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (hlo : netV10 n ≤ v.val) (hhi : v.val < netV11 n) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true := by
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val) _ = true
  rw [rawPred_of_V10 mode n h s t0 t1 pre hlo hhi]
  dsimp only
  exact constCircuit_eval _ true _

lemma eval_V12 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (hlo : netV12 n ≤ v.val) (hhi : v.val < netV13 n) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      bne (bne (wireAt n x (netE1 n + (v.val - netV12 n)))
               (wireAt n x (netE11 n + (v.val - netV12 n))))
          (wireAt n x (netE11 n + (v.val - netV12 n) + n)) =
        (if hlt : v.val - netV12 n < n then zmod2ToBool (s ⟨v.val - netV12 n, hlt⟩) else false) := by
  set i := v.val - netV12 n
  have hexp : expectedInc n v.val = [netE1 n + i, netE11 n + i, netE11 n + i + n] := by
    unfold expectedInc
    rw [(inOut_of_V12 hlo hhi).1, (inOut_of_V12 hlo hhi).2, List.append_nil]
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
    (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) = true ↔ _
  rw [rawPred_of_V12 mode n h s t0 t1 pre hlo hhi,
      (synCheckCircuit_wf_and_eval _ _).2.1, beq_iff_eq,
      vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x 0 (by rw [hexp]; simp),
      vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x 1 (by rw [hexp]; simp),
      vertexInp_buildQCSDNet _ _ _ _ _ _ _ v x 2 (by rw [hexp]; simp)]
  simp only [hexp, List.getD_cons_zero, List.getD_cons_succ]
  rfl

lemma eval_V15_fa (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    {j node u : ℕ} (hlo : netV15 n ≤ v.val) (hhi : v.val < netV16 n)
    (hdec : decodeTreeVert (treeLog n + 1) (v.val - netV15 n) = (j, node, u))
    (hu0 : u ≠ 0) :
    let r := treeLog n + 1
    let b := u - 1
    let base := netE12 n + treeEdgeOff r j + node * (2 * j + 1)
    let eCin := base + 2 * b
    let eA := if j = 1 then netE2 n + 2 * node
              else netE12 n + treeEdgeOff r (j - 1) + (2 * node) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b
    let eB := if j = 1 then netE2 n + 2 * node + 1
              else netE12 n + treeEdgeOff r (j - 1) + (2 * node + 1) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      (wireAt n x (base + 2 * b + 1) = bne (bne (wireAt n x eA) (wireAt n x eB)) (wireAt n x eCin) ∧
       wireAt n x (base + 2 * b + 2) =
         ((wireAt n x eA && wireAt n x eB) ||
          ((wireAt n x eA && wireAt n x eCin) || (wireAt n x eB && wireAt n x eCin))) ∧
       (mode = 2 ∧ j = r →
         t0 < 2 ^ r ∧ t1 < 2 ^ r ∧
         wireAt n x eA = t0.testBit b ∧ wireAt n x eB = t1.testBit b)) := by
  dsimp only
  set r := treeLog n + 1
  set b := u - 1
  set base := netE12 n + treeEdgeOff r j + node * (2 * j + 1)
  set eCin := base + 2 * b
  set eA := if j = 1 then netE2 n + 2 * node
            else netE12 n + treeEdgeOff r (j - 1) + (2 * node) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b
  set eB := if j = 1 then netE2 n + 2 * node + 1
            else netE12 n + treeEdgeOff r (j - 1) + (2 * node + 1) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b
  have hexp : expectedInc n v.val = [eA, eB, eCin, base + 2 * b + 1, base + 2 * b + 2] := by
    unfold expectedInc
    rw [inEdges_of_V15 hlo hhi hdec, outEdges_of_V15 hlo hhi hdec]
    simp only [hu0, ↓reduceIte]
    by_cases hj1 : j = 1 <;> simp [hj1, eA, eB, eCin, base, r, b]
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
    (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) = true ↔ _
  rw [rawPred_of_V15 mode n h s t0 t1 pre hlo hhi hdec]
  dsimp only
  simp only [hu0, ↓reduceIte]
  have hi0 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 0 (by rw [hexp]; simp)
  have hi1 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 1 (by rw [hexp]; simp)
  have hi2 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 2 (by rw [hexp]; simp)
  have hi3 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 3 (by rw [hexp]; simp)
  have hi4 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 4 (by rw [hexp]; simp)
  simp only [hexp, List.getD_cons_zero, List.getD_cons_succ] at hi0 hi1 hi2 hi3 hi4
  by_cases hsep : mode = 2 ∧ j = treeLog n + 1
  · rw [ite_pos hsep, (sepFullAdderCircuit_spec _ _ _ _).2.1, hi0, hi1, hi2, hi3, hi4]
    have hsep' : mode = 2 ∧ j = r := hsep
    simp only [hsep', and_self, forall_true_left, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    tauto
  · rw [ite_neg hsep, (fullAdderCircuit_wf_and_eval _).2.1, hi0, hi1, hi2, hi3, hi4]
    have hsep' : ¬(mode = 2 ∧ j = r) := hsep
    simp only [hsep', IsEmpty.forall_iff, and_true, Bool.and_eq_true, beq_iff_eq]
    rfl

lemma eval_V17 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (hlo : netV17 n ≤ v.val) (hhi : v.val < netV18 n) :
    let b := v.val - netV17 n
    let r := treeLog n + 1
    let W := treeLog n + 2
    let eSum := netE12 n + treeEdgeOff r r + sumWireLoc r b
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      (if mode = 0 then
         t0 < 2 ^ W ∧ wireAt n x eSum = t0.testBit b ∧ wireAt n x (netE13 n + b + 1) = false
       else if mode = 1 then
         wireAt n x (netE13 n + b + 1) =
           (if t0.testBit b then (wireAt n x eSum && wireAt n x (netE13 n + b))
            else (wireAt n x eSum || wireAt n x (netE13 n + b)))
       else
         wireAt n x (netE13 n + b + 1) = false) := by
  dsimp only
  set b := v.val - netV17 n
  set r := treeLog n + 1
  set eSum := netE12 n + treeEdgeOff r r + sumWireLoc r b
  have hexp : expectedInc n v.val = [eSum, netE13 n + b, netE13 n + b + 1] := by
    unfold expectedInc
    rw [(inOut_of_V17 hlo hhi).1, (inOut_of_V17 hlo hhi).2]
    rfl
  unfold vertexSat
  change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val)
    (vertexInp (buildQCSDNet mode n h s t0 t1 pre) v x) = true ↔ _
  rw [rawPred_of_V17 mode n h s t0 t1 pre hlo hhi]
  dsimp only
  have hi0 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 0 (by rw [hexp]; simp)
  have hi1 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 1 (by rw [hexp]; simp)
  have hi2 := vertexInp_buildQCSDNet mode n h s t0 t1 pre v x 2 (by rw [hexp]; simp)
  simp only [hexp, List.getD_cons_zero, List.getD_cons_succ] at hi0 hi1 hi2
  by_cases hm0 : mode = 0
  · simp only [hm0, ↓reduceIte, (exactCmpStepCircuit_spec _ _ _).2.1, hi0, hi2,
               Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
    rfl
  · simp only [hm0, ↓reduceIte]
    by_cases hm1 : mode = 1
    · simp only [hm1, ↓reduceIte, (borrowStepCircuit_wf_and_eval _ _).2.1, hi0, hi1, hi2, beq_iff_eq]
      rfl
    · simp only [hm1, ↓reduceIte, (sepCmpStepCircuit_spec _).2.1, hi2, beq_iff_eq]

lemma eval_V18 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (v : Fin (netVertCount n)) (x : Fin (netEdgeCount n) → Bool)
    (hlo : netV18 n ≤ v.val) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true ↔
      if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then True
      else wireAt n x (netE13 n + (treeLog n + 2)) = false := by
  have hexp : expectedInc n v.val = [netE13 n + (treeLog n + 2)] := by
    unfold expectedInc
    rw [(inOut_of_V18 hlo).1, (inOut_of_V18 hlo).2, List.append_nil]
  by_cases hc : mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2))
  · rw [ite_pos hc]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    unfold vertexSat
    change QCSD_evalCircuit (rawPred mode n h s t0 t1 pre v.val) _ = true
    rw [rawPred_of_V18 mode n h s t0 t1 pre hlo, ite_pos hc]
    exact constCircuit_eval 1 true _
  · rw [ite_neg hc]
    have hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit (some false) := by
      rw [rawPred_of_V18 mode n h s t0 t1 pre hlo, ite_neg hc]
    exact eval_pin_vertex mode n h s t0 t1 pre v x _ (some false) hpred hexp

/-! ### Pure `ovlInLocal` Parity and `treeWireVal` Helpers -/

lemma ovlInLocal_parity (n : ℕ) (h : Fin n → ZMod 2) (w : Fin (2 * n) → Bool)
    (tk : ℕ) {f : ℕ → Bool}
    (hf : ∀ k < 2 * paramJ n * paramL n,
      f k = mulWiresCraw n h w (k / (2 * paramJ n)) (k % (2 * paramJ n))) :
    linearMapTarget (ovlInLocal (paramJ n) (paramL n) tk).length (fun _ _ => true)
      (fun i => f ((ovlInLocal (paramJ n) (paramL n) tk).getD i 0)) 0 =
    mulWiresZ n h w tk := by
  set J := paramJ n
  set L := paramL n
  have hJ : 0 < J := paramJ_pos n
  have hmod : tk % J < J := Nat.mod_lt tk hJ
  have hspec := (ovlInLocal_spec (J := J) (L := L) (tk := tk) hJ).2
  unfold mulWiresZ twoLayerPolyMulBit
  change linearMapTarget (ovlInLocal J L tk).length (fun _ _ => true)
      (fun i => f ((ovlInLocal J L tk).getD i 0)) 0 =
    bne (if tk / J < L then mulWiresCraw n h w (tk / J) (tk % J) else false)
        (if 0 < tk / J ∧ tk / J - 1 < L then mulWiresCraw n h w (tk / J - 1) (J + tk % J) else false)
  by_cases hhi : 0 < tk / J ∧ tk / J - 1 < L
  · have hk_hi_mem : (tk / J - 1) * (2 * J) + (J + tk % J) ∈ ovlInLocal J L tk := by
      unfold ovlInLocal; simp [hhi]
    have hk_hi_lt := hspec _ hk_hi_mem
    obtain ⟨hd_hi, hm_hi⟩ := mul_add_div_mod (W := 2 * J) (q := tk / J - 1) (p := J + tk % J)
      (by omega) (by omega)
    have hf_hi : f ((tk / J - 1) * (2 * J) + (J + tk % J)) =
        mulWiresCraw n h w (tk / J - 1) (J + tk % J) := by
      rw [hf _ hk_hi_lt, hd_hi, hm_hi]
    by_cases hlo : tk / J < L
    · have hk_lo_mem : (tk / J) * (2 * J) + tk % J ∈ ovlInLocal J L tk := by
        unfold ovlInLocal; simp [hlo]
      have hk_lo_lt := hspec _ hk_lo_mem
      obtain ⟨hd_lo, hm_lo⟩ := mul_add_div_mod (W := 2 * J) (q := tk / J) (p := tk % J)
        (by omega) (by omega)
      have hf_lo : f ((tk / J) * (2 * J) + tk % J) =
          mulWiresCraw n h w (tk / J) (tk % J) := by
        rw [hf _ hk_lo_lt, hd_lo, hm_lo]
      have hovl : ovlInLocal J L tk =
          [(tk / J - 1) * (2 * J) + (J + tk % J), (tk / J) * (2 * J) + tk % J] := by
        unfold ovlInLocal; simp [hhi, hlo]
      rw [hovl, ite_pos hlo, ite_pos hhi]
      change bne (bne false (f ((tk / J - 1) * (2 * J) + (J + tk % J))))
                 (f ((tk / J) * (2 * J) + tk % J)) = _
      rw [hf_hi, hf_lo]
      generalize mulWiresCraw n h w (tk / J) (tk % J) = blo,
                 mulWiresCraw n h w (tk / J - 1) (J + tk % J) = bhi
      cases blo <;> cases bhi <;> rfl
    · have hovl : ovlInLocal J L tk = [(tk / J - 1) * (2 * J) + (J + tk % J)] := by
        unfold ovlInLocal; simp [hhi, hlo]
      rw [hovl, ite_neg hlo, ite_pos hhi]
      change bne false (f ((tk / J - 1) * (2 * J) + (J + tk % J))) = _
      rw [hf_hi]
  · by_cases hlo : tk / J < L
    · have hk_lo_mem : (tk / J) * (2 * J) + tk % J ∈ ovlInLocal J L tk := by
        unfold ovlInLocal; simp [hlo]
      have hk_lo_lt := hspec _ hk_lo_mem
      obtain ⟨hd_lo, hm_lo⟩ := mul_add_div_mod (W := 2 * J) (q := tk / J) (p := tk % J)
        (by omega) (by omega)
      have hf_lo : f ((tk / J) * (2 * J) + tk % J) =
          mulWiresCraw n h w (tk / J) (tk % J) := by
        rw [hf _ hk_lo_lt, hd_lo, hm_lo]
      have hovl : ovlInLocal J L tk = [(tk / J) * (2 * J) + tk % J] := by
        unfold ovlInLocal; rw [ite_neg hhi, ite_pos hlo]; rfl
      rw [hovl, ite_pos hlo, ite_neg hhi]
      change bne false (f ((tk / J) * (2 * J) + tk % J)) = _
      rw [hf_lo]
      cases mulWiresCraw n h w (tk / J) (tk % J) <;> rfl
    · have hovl : ovlInLocal J L tk = [] := by
        unfold ovlInLocal; rw [ite_neg hhi, ite_neg hlo]; rfl
      rw [hovl, ite_neg hlo, ite_neg hhi]
      rfl

lemma treeWireVal_even (n : ℕ) (w : Fin (2 * n) → Bool)
    {j node b : ℕ} (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hb : b ≤ j) :
    treeWireVal n w (treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b) =
      rippleCarry (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node))
                  (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node + 1)) b := by
  have hw_lt : 2 * b < 2 * j + 1 := by omega
  have hdec := decodeTreeEdge_encode hj1 hjr hnode hw_lt
  unfold treeWireVal
  dsimp only
  rw [hdec]
  dsimp only
  rcases eq_or_lt_of_le hb with rfl | hb_lt
  · have hncond : ¬((2 * b) % 2 = 0 ∧ 2 * b < 2 * b) := by omega
    rw [ite_neg hncond]
    simp only [↓reduceIte]
    rcases Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega) with ⟨m, rfl⟩
    simp [treeLevelBits, rippleSum]
  · have hcond : (2 * b) % 2 = 0 ∧ 2 * b < 2 * j := by omega
    rw [ite_pos hcond]
    have hd : (2 * b) / 2 = b := by omega
    rw [hd]

lemma treeWireVal_odd (n : ℕ) (w : Fin (2 * n) → Bool)
    {j node b : ℕ} (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hb : b < j) :
    treeWireVal n w (treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + (2 * b + 1)) =
      bne (bne (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node) b)
               (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node + 1) b))
          (rippleCarry (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node))
                       (treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node + 1)) b) := by
  have hw_lt : 2 * b + 1 < 2 * j + 1 := by omega
  have hdec := decodeTreeEdge_encode hj1 hjr hnode hw_lt
  unfold treeWireVal
  dsimp only
  rw [hdec]
  dsimp only
  have hncond : ¬((2 * b + 1) % 2 = 0 ∧ 2 * b + 1 < 2 * j) := by omega
  have hne : 2 * b + 1 ≠ 2 * j := by omega
  have hd : (2 * b + 1) / 2 = b := by omega
  rw [ite_neg hncond]
  simp only [hne, ↓reduceIte, hd]
  rcases Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega) with ⟨m, rfl⟩
  have hbm : b < m + 1 := hb
  simp [treeLevelBits, rippleSum, hbm]

lemma treeWireVal_sumWireLoc (n : ℕ) (w : Fin (2 * n) → Bool)
    {j node b : ℕ} (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hb : b ≤ j) :
    treeWireVal n w (treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + sumWireLoc j b) =
      treeLevelBits (2 * treeM n) (padLeaves n w) j node b := by
  have hsw_lt : sumWireLoc j b < 2 * j + 1 := sumWireLoc_lt hb
  obtain ⟨hncond, hbit⟩ := (sumWireLoc_iff hj1 hsw_lt hb).mpr rfl
  have hdec := decodeTreeEdge_encode hj1 hjr hnode hsw_lt
  unfold treeWireVal
  dsimp only
  rw [hdec]
  dsimp only
  rw [ite_neg hncond, hbit]

/-! ### Mode Validity & Bijection Between Satisfying Assignments and Valid Interfaces -/

def ModeWeightCond (mode : ℕ) (wt0 wt1 t0 t1 : ℕ) : Prop :=
  if mode = 0 then wt0 + wt1 = t0
  else if mode = 1 then wt0 + wt1 ≤ t0
  else wt0 = t0 ∧ wt1 = t1

def ValidModeIface (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (w : Fin (2 * n) → Bool) : Prop :=
  let p := decodeIfaceVec n w
  (∀ i : Fin (2 * n), i.val < pre.length → w i = pre.getD i.val false) ∧
  (∀ k : Fin n, p.1 k + twoLayerCycMul n h p.2 k = s k) ∧
  ModeWeightCond mode (QCSD_wt p.1) (QCSD_wt p.2) t0 t1

lemma fwdSt1InIndices_getD_lt {n J L2 j2 i : ℕ}
    (hi : i < (fwdSt1InIndices n J L2 j2).length) :
    (fwdSt1InIndices n J L2 j2).getD i 0 < n := by
  rw [getD_eq_getElem_of_lt _ 0 hi]
  have hmem : (fwdSt1InIndices n J L2 j2)[i] ∈ fwdSt1InIndices n J L2 j2 := List.getElem_mem hi
  unfold fwdSt1InIndices at hmem
  exact List.mem_range.mp (List.mem_of_mem_filter hmem)

lemma div_mul_add_mod (a b : ℕ) : (a / b) * b + a % b = a := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod a b

lemma mod_add_mul_div (a b : ℕ) : a % b + b * (a / b) = a := by
  rw [Nat.add_comm]
  exact Nat.div_add_mod a b

/-- Forward propagation Stage A: interface pinning, copy/leaf padding, and 2-layer syndrome wires. -/
lemma sat_imp_mul_and_syn (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (x : Fin (netEdgeCount n) → Bool)
    (hsat : ∀ v : Fin (netVertCount n), vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true) :
    let w : Fin (2 * n) → Bool :=
      fun i => x ⟨i.val, lt_of_lt_of_le i.isLt (netE1_le_netEdgeCount n)⟩
    (∀ i : Fin (2 * n), i.val < pre.length → w i = pre.getD i.val false) ∧
    (∀ e < netE12 n, wireAt n x e = rawExtWire mode n h t0 w e) ∧
    (∀ k : Fin n, (decodeIfaceVec n w).1 k + twoLayerCycMul n h (decodeIfaceVec n w).2 k = s k) := by
  dsimp only
  set w : Fin (2 * n) → Bool :=
    fun i => x ⟨i.val, lt_of_lt_of_le i.isLt (netE1_le_netEdgeCount n)⟩
  set J := paramJ n
  set L := paramL n
  set L1 := paramL1 n
  set L2 := paramL2 n
  have h2J : 0 < 2 * J := by have := paramJ_pos n; omega
  have hL1 : 0 < L1 := one_le_paramL1 n
  have hL2 : 0 < L2 := one_le_paramL2 n
  have hL_mul : L = L1 * L2 := paramL_eq_mul n
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netV_chain n with
    ⟨hv0, hv1_le, hv2_le, hv3_le, hv4_le, hv5_le, hv6_le, hv7_le, hv8_le, hv9_le,
     hv10_le, hv11_le, hv12_le, hv13_le, hv14_le, hv15_le, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with
    ⟨he0_le, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hE0_val : ∀ i (hi : i < 2 * n), wireAt n x i = w ⟨i, hi⟩ := by
    intro i hi
    rw [wireAt_lt x (lt_of_lt_of_le hi (netE1_le_netEdgeCount n))]
  have hpre : ∀ i : Fin (2 * n), i.val < pre.length → w i = pre.getD i.val false := by
    intro i hi
    have hv_lt1 : i.val < netV1 n := i.isLt
    have hv_lt : i.val < netVertCount n := by omega
    have hexp : expectedInc n i.val = [i.val] := by
      unfold expectedInc; rw [(inOut_of_V0 hv_lt1).1, (inOut_of_V0 hv_lt1).2]; simp [netE0]
    have hp := (eval_pin_vertex mode n h s t0 t1 pre ⟨i.val, hv_lt⟩ x i.val (some (pre.getD i.val false))
      (by rw [rawPred_of_V0 _ _ _ _ _ _ _ hv_lt1, ite_pos hi]) hexp).mp (hsat ⟨i.val, hv_lt⟩)
    dsimp only at hp
    rw [← hp, hE0_val i.val i.isLt]
  have hcopy : ∀ i (hi : i < 2 * n),
      wireAt n x (netE1 n + i) = w ⟨i, hi⟩ ∧
      wireAt n x (netE2 n + (if i < n then i else treeM n + (i - n))) = w ⟨i, hi⟩ := by
    intro i hi
    set v := netV1 n + i
    have hv1 : netV1 n ≤ v := Nat.le_add_right _ _
    have hv2 : v < netV2 n := by change 2 * n + i < 4 * n; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV1 n = i := Nat.add_sub_cancel_left _ _
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      [netE0 n + i]
      [netE1 n + i, netE2 n + (if i < n then i else treeM n + (i - n))]
      (fun _ _ => true)
      (rawPred_of_V1 _ _ _ _ _ _ _ hv1 hv2)
      (by rw [(inOut_of_V1 hv1 hv2).1, hsub])
      (by rw [(inOut_of_V1 hv1 hv2).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    have h0 := hlin 0 (by simp)
    have h1 := hlin 1 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_singleton, netE0, Nat.zero_add] at h0 h1
    have htgt : ∀ k, linearMapTarget 1 (fun _ _ => true) (fun m => wireAt n x ([i].getD m 0)) k = w ⟨i, hi⟩ := by
      intro k; change bne false (wireAt n x i) = _; rw [hE0_val i hi]; cases w ⟨i, hi⟩ <;> rfl
    rw [htgt 0] at h0; rw [htgt 1] at h1
    exact ⟨h0, h1⟩
  have hE2_val : ∀ leaf < 2 * treeM n, wireAt n x (netE2 n + leaf) = padLeaves n w leaf := by
    intro leaf hleaf
    unfold padLeaves
    by_cases hl1 : leaf < n
    · simp only [hl1, ↓reduceDIte]
      have hc := (hcopy leaf (by omega)).2
      simpa [hl1] using hc
    · simp only [hl1, ↓reduceDIte]
      by_cases hl2 : leaf < treeM n
      · simp only [hl2, ↓reduceDIte]
        set v := netV13 n + (leaf - n)
        have hv13 : netV13 n ≤ v := Nat.le_add_right _ _
        have hv14 : v < netV14 n := by have : netV14 n = netV13 n + (treeM n - n) := rfl; omega
        have hv_lt : v < netVertCount n := by omega
        have hsub : v - netV13 n = leaf - n := Nat.add_sub_cancel_left _ _
        have hexp : expectedInc n v = [netE2 n + leaf] := by
          unfold expectedInc; rw [(inOut_of_V13 hv13 hv14).1, (inOut_of_V13 hv13 hv14).2, hsub]
          simp [show netE2 n + n + (leaf - n) = netE2 n + leaf by omega]
        exact (eval_pin_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x (netE2 n + leaf) (some false)
          (rawPred_of_V13 _ _ _ _ _ _ _ hv13 hv14) hexp).mp (hsat ⟨v, hv_lt⟩)
      · simp only [hl2, ↓reduceDIte]
        by_cases hl3 : leaf < treeM n + n
        · simp only [hl3, ↓reduceDIte]
          set i := n + (leaf - treeM n)
          have hi : i < 2 * n := by omega
          have hc := (hcopy i hi).2
          have hni : ¬(i < n) := by omega
          have heq_l : treeM n + (i - n) = leaf := by omega
          simpa [hni, heq_l] using hc
        · simp only [hl3, ↓reduceDIte]
          set v := netV14 n + (leaf - (treeM n + n))
          have hv14 : netV14 n ≤ v := Nat.le_add_right _ _
          have hv15 : v < netV15 n := by have : netV15 n = netV14 n + (treeM n - n) := rfl; omega
          have hv_lt : v < netVertCount n := by omega
          have hsub : v - netV14 n = leaf - (treeM n + n) := Nat.add_sub_cancel_left _ _
          have hexp : expectedInc n v = [netE2 n + leaf] := by
            unfold expectedInc; rw [(inOut_of_V14 hv14 hv15).1, (inOut_of_V14 hv14 hv15).2, hsub]
            simp [show netE2 n + treeM n + n + (leaf - (treeM n + n)) = netE2 n + leaf by omega]
          exact (eval_pin_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x (netE2 n + leaf) (some false)
            (rawPred_of_V14 _ _ _ _ _ _ _ hv14 hv15) hexp).mp (hsat ⟨v, hv_lt⟩)
  have hE3_val : ∀ idx < n, wireAt n x (netE3 n + idx) = hBit n h idx := by
    intro idx hidx
    set v := netV2 n + idx
    have hv2 : netV2 n ≤ v := Nat.le_add_right _ _
    have hv3 : v < netV3 n := by have : netV2 n = 4 * n := rfl; have : netV3 n = 5 * n := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV2 n = idx := Nat.add_sub_cancel_left _ _
    have hexp : expectedInc n v = [netE3 n + idx] := by
      unfold expectedInc; rw [(inOut_of_V2 hv2 hv3).1, (inOut_of_V2 hv2 hv3).2, hsub]; rfl
    have hpred : rawPred mode n h s t0 t1 pre v = pinBitCircuit (some (hBit n h idx)) := by
      rw [rawPred_of_V2 _ _ _ _ _ _ _ hv2 hv3, hsub]; rfl
    exact (eval_pin_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x (netE3 n + idx) (some (hBit n h idx))
      hpred hexp).mp (hsat ⟨v, hv_lt⟩)
  have hE4_val : ∀ idx < 2 * J * L,
      wireAt n x (netE4 n + idx) = mulWiresYa n h ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    set j2 := q / L1; set q1 := q % L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hj2 : j2 < L2 := by
      have hk : idx < (L2 * L1) * (2 * J) := by
        calc idx < 2 * J * (L1 * L2) := hidx'
             _ = (L2 * L1) * (2 * J) := by ring
      have hrem : q < L2 * L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    set v := netV3 n + j2
    have hv3 : netV3 n ≤ v := Nat.le_add_right _ _
    have hv4 : v < netV4 n := by have hV4 : netV4 n = netV3 n + L2 := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV3 n = j2 := Nat.add_sub_cancel_left _ _
    set inList := fwdSt1InIndices n J L2 j2
    set outL := (List.range (2 * J * L1)).map
      (fun k => netE4 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      (inList.map (fun m => netE3 n + m)) outL (fwdSt1Mat J L1 (paramOmegaExp n) inList)
      (by rw [rawPred_of_V3 _ _ _ _ _ _ _ hv3 hv4, hsub]; simp [inList, outL, J, L1, L2])
      (by rw [(inOut_of_V3 hv3 hv4).1, hsub])
      (by rw [(inOut_of_V3 hv3 hv4).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q1 * (2 * J) + p
    have hk_lt : k < 2 * J * L1 := by
      have : q1 * (2 * J) + p < (q1 + 1) * (2 * J) := by
        have : (q1 + 1) * (2 * J) = q1 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L1]; exact Nat.mul_le_mul_right _ hq1)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : j2 * L1 + q1 = q := div_mul_add_mod q L1
    have hidx_eq : (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) = idx := by
      rw [hdk, hmk, hq_eq]
      exact div_mul_add_mod idx (2 * J)
    have he_eq : netE4 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) = netE4 n + idx := by omega
    rw [he_eq] at hstep
    rw [hstep]
    unfold mulWiresYa twoLayerFwdSt1
    dsimp only
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < inList.length := by simpa [inList, J, L2] using hi
    rw [getD_map_nat inList _ hi', hE3_val _ (fwdSt1InIndices_getD_lt hi')]
  have hE5_val : ∀ idx < 2 * J * L,
      wireAt n x (netE5 n + idx) = mulWiresFa n h (idx / (2 * J)) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    have hq : q < L1 * L2 := by
      rw [← hL_mul]; exact Nat.div_lt_of_lt_mul hidx
    set q1 := q % L1; set q2 := q / L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hq2 : q2 < L2 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hq)
    set v := netV4 n + q1
    have hv4 : netV4 n ≤ v := Nat.le_add_right _ _
    have hv5 : v < netV5 n := by have : netV5 n = netV4 n + L1 := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV4 n = q1 := Nat.add_sub_cancel_left _ _
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE4 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE5 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      inL outL (st2Mat J L1 L2 (paramOmegaExp n))
      (by rw [rawPred_of_V4 _ _ _ _ _ _ _ hv4 hv5]; simp [inL, outL, J, L1, L2])
      (by rw [(inOut_of_V4 hv4 hv5).1, hsub])
      (by rw [(inOut_of_V4 hv4 hv5).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q2 * (2 * J) + p
    have hk_lt : k < 2 * J * L2 := by
      have : q2 * (2 * J) + p < (q2 + 1) * (2 * J) := by
        have : (q2 + 1) * (2 * J) = q2 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L2]; exact Nat.mul_le_mul_right _ hq2)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : q1 + L1 * q2 = q := mod_add_mul_div q L1
    have he_eq : netE5 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) = netE5 n + idx := by
      rw [hdk, hmk, hq_eq, Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he_eq] at hstep; rw [hstep]
    unfold mulWiresFa twoLayerFwdSt2
    dsimp only
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := hm
    rw [getD_range_map_nat _ hm']
    have hloc_lt : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he4_eq : netE4 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE4 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    rw [he4_eq, hE4_val _ hloc_lt]
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [hd1, hm1, hd2, hm2]
  have hE6_val : ∀ idx < 2 * J * L,
      wireAt n x (netE6 n + idx) = mulWiresYb n w ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    set j2 := q / L1; set q1 := q % L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hj2 : j2 < L2 := by
      have hk : idx < (L2 * L1) * (2 * J) := by
        calc idx < 2 * J * (L1 * L2) := hidx'
             _ = (L2 * L1) * (2 * J) := by ring
      have hrem : q < L2 * L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    set v := netV5 n + j2
    have hv5 : netV5 n ≤ v := Nat.le_add_right _ _
    have hV6_eq : netV6 n = netV5 n + L2 := by unfold netV5 netV6; dsimp only [L2]; ring
    have hv6 : v < netV6 n := by omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV5 n = j2 := Nat.add_sub_cancel_left _ _
    set inList := fwdSt1InIndices n J L2 j2
    set outL := (List.range (2 * J * L1)).map
      (fun k => netE6 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      (inList.map (fun m => netE1 n + n + m)) outL (fwdSt1Mat J L1 (paramOmegaExp n) inList)
      (by rw [rawPred_of_V5 _ _ _ _ _ _ _ hv5 hv6, hsub]; simp [inList, outL, J, L1, L2])
      (by rw [(inOut_of_V5 hv5 hv6).1, hsub])
      (by rw [(inOut_of_V5 hv5 hv6).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q1 * (2 * J) + p
    have hk_lt : k < 2 * J * L1 := by
      have : q1 * (2 * J) + p < (q1 + 1) * (2 * J) := by
        have : (q1 + 1) * (2 * J) = q1 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L1]; exact Nat.mul_le_mul_right _ hq1)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : j2 * L1 + q1 = q := div_mul_add_mod q L1
    have he_eq : netE6 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) = netE6 n + idx := by
      rw [hdk, hmk, hq_eq, Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he_eq] at hstep; rw [hstep]
    unfold mulWiresYb twoLayerFwdSt1
    dsimp only
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < inList.length := by simpa [inList, J, L2] using hi
    have hlt_n : inList.getD i 0 < n := fwdSt1InIndices_getD_lt hi'
    rw [getD_map_nat inList _ hi']
    have he1_eq : netE1 n + n + inList.getD i 0 = netE1 n + (n + inList.getD i 0) := by omega
    rw [he1_eq, (hcopy (n + inList.getD i 0) (by omega)).1]
    unfold e1Bit
    rw [dite_pos (fwdSt1InIndices_getD_lt hi')]
  have hE7_val : ∀ idx < 2 * J * L,
      wireAt n x (netE7 n + idx) = mulWiresFb n w (idx / (2 * J)) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    have hq : q < L1 * L2 := by rw [← hL_mul]; exact Nat.div_lt_of_lt_mul hidx
    set q1 := q % L1; set q2 := q / L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hq2 : q2 < L2 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hq)
    set v := netV6 n + q1
    have hv6 : netV6 n ≤ v := Nat.le_add_right _ _
    have hV7_eq : netV7 n = netV6 n + L1 := by unfold netV6 netV7; dsimp only [L1]; ring
    have hv7 : v < netV7 n := by omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV6 n = q1 := Nat.add_sub_cancel_left _ _
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE6 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE7 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      inL outL (st2Mat J L1 L2 (paramOmegaExp n))
      (by rw [rawPred_of_V6 _ _ _ _ _ _ _ hv6 hv7]; simp [inL, outL, J, L1, L2])
      (by rw [(inOut_of_V6 hv6 hv7).1, hsub])
      (by rw [(inOut_of_V6 hv6 hv7).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q2 * (2 * J) + p
    have hk_lt : k < 2 * J * L2 := by
      have : q2 * (2 * J) + p < (q2 + 1) * (2 * J) := by
        have : (q2 + 1) * (2 * J) = q2 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L2]; exact Nat.mul_le_mul_right _ hq2)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : q1 + L1 * q2 = q := mod_add_mul_div q L1
    have he_eq : netE7 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) = netE7 n + idx := by
      rw [hdk, hmk, hq_eq, Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he_eq] at hstep; rw [hstep]
    unfold mulWiresFb twoLayerFwdSt2
    dsimp only
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := hm
    rw [getD_range_map_nat _ hm']
    have hloc_lt : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he6_eq : netE6 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE6 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    rw [he6_eq, hE6_val _ hloc_lt]
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [hd1, hm1, hd2, hm2]
  have hE8_val : ∀ idx < 2 * J * L,
      wireAt n x (netE8 n + idx) = mulWiresFc n h w (idx / (2 * J)) (idx % (2 * J)) := by
    intro idx hidx
    set q := idx / (2 * J); set p := idx % (2 * J)
    have hq : q < L := Nat.div_lt_of_lt_mul hidx
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    set v := netV7 n + q
    have hv7 : netV7 n ≤ v := Nat.le_add_right _ _
    have hv8 : v < netV8 n := by have : netV8 n = netV7 n + L := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV7 n = q := Nat.add_sub_cancel_left _ _
    have hbil := (eval_V7 mode n h s t0 t1 pre ⟨v, hv_lt⟩ x hv7 hv8).mp (hsat ⟨v, hv_lt⟩) p hp
    dsimp only at hbil
    rw [hsub] at hbil
    have he8_eq : netE8 n + q * (2 * J) + p = netE8 n + idx := by
      rw [Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he8_eq] at hbil; rw [hbil]
    unfold mulWiresFc ringMulBits
    apply bilinearMapTarget_congr h2J
    intro m hm
    by_cases hm1 : m < 2 * J
    · have hm1' : m < 2 * paramJ n := hm1
      simp only [hm1', ↓reduceIte]
      have hlt5 : q * (2 * J) + m < 2 * J * L := by
        have : q * (2 * J) + m < (q + 1) * (2 * J) := by
          have : (q + 1) * (2 * J) = q * (2 * J) + 2 * J := by ring
          omega
        exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L]; exact Nat.mul_le_mul_right _ hq)
      have he5_eq : netE5 n + q * (2 * J) + m = netE5 n + (q * (2 * J) + m) := by omega
      obtain ⟨hd, hmd⟩ := mul_add_div_mod h2J hm1
      rw [he5_eq, hE5_val _ hlt5, hd, hmd]
    · have hm1' : ¬(m < 2 * paramJ n) := hm1
      simp only [hm1', ↓reduceIte]
      have hsub_m : m - 2 * J < 2 * J := by omega
      have hlt7 : q * (2 * J) + (m - 2 * J) < 2 * J * L := by
        have : q * (2 * J) + (m - 2 * J) < (q + 1) * (2 * J) := by
          have : (q + 1) * (2 * J) = q * (2 * J) + 2 * J := by ring
          omega
        exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L]; exact Nat.mul_le_mul_right _ hq)
      have he7_eq : netE7 n + q * (2 * J) + (m - 2 * J) = netE7 n + (q * (2 * J) + (m - 2 * J)) := by omega
      obtain ⟨hd, hmd⟩ := mul_add_div_mod h2J hsub_m
      rw [he7_eq, hE7_val _ hlt7, hd, hmd]
  have hE9_val : ∀ idx < 2 * J * L,
      wireAt n x (netE9 n + idx) = mulWiresYc n h w ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    set j2 := q / L1; set q1 := q % L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hj2 : j2 < L2 := by
      have hk : idx < (L2 * L1) * (2 * J) := by
        calc idx < 2 * J * (L1 * L2) := hidx'
             _ = (L2 * L1) * (2 * J) := by ring
      have hrem : q < L2 * L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hrem)
    set v := netV8 n + j2
    have hv8 : netV8 n ≤ v := Nat.le_add_right _ _
    have hv9 : v < netV9 n := by have : netV9 n = netV8 n + L2 := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV8 n = j2 := Nat.add_sub_cancel_left _ _
    set inL := (List.range (2 * J * L1)).map
      (fun m => netE8 n + (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L1)).map
      (fun m => netE9 n + (j2 * L1 + m / (2 * J)) * (2 * J) + m % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      inL outL (fullSt1Mat J L1 L2 (paramInvOmegaExp n) j2)
      (by rw [rawPred_of_V8 _ _ _ _ _ _ _ hv8 hv9, hsub]; simp [inL, outL, J, L1, L2])
      (by rw [(inOut_of_V8 hv8 hv9).1, hsub])
      (by rw [(inOut_of_V8 hv8 hv9).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q1 * (2 * J) + p
    have hk_lt : k < 2 * J * L1 := by
      have : q1 * (2 * J) + p < (q1 + 1) * (2 * J) := by
        have : (q1 + 1) * (2 * J) = q1 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L1]; exact Nat.mul_le_mul_right _ hq1)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : j2 * L1 + q1 = q := div_mul_add_mod q L1
    have he_eq : netE9 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) = netE9 n + idx := by
      rw [hdk, hmk, hq_eq, Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he_eq] at hstep; rw [hstep]
    unfold mulWiresYc twoLayerInvSt1
    dsimp only
    have hinL_len : inL.length = 2 * paramJ n * paramL1 n := by simp [inL, J, L1]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L1 := hm
    rw [getD_range_map_nat _ hm']
    have hloc_lt : (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J) < 2 * J * L := by
      have hcomm : L2 * (m / (2 * J)) = (m / (2 * J)) * L2 := Nat.mul_comm _ _
      rw [hcomm, hL_mul, Nat.mul_comm L1 L2]
      exact affine_stride_lt h2J hj2 hm'
    have he8_eq : netE8 n + (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J) =
        netE8 n + ((L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J)) := by omega
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    rw [he8_eq, hE8_val _ hloc_lt, hd1, hm1]
  have hE10_val : ∀ idx < 2 * J * L,
      wireAt n x (netE10 n + idx) = mulWiresCraw n h w (idx / (2 * J)) (idx % (2 * J)) := by
    intro idx hidx
    have hidx' : idx < 2 * J * (L1 * L2) := by rwa [← hL_mul]
    set q := idx / (2 * J); set p := idx % (2 * J)
    have hq : q < L1 * L2 := by rw [← hL_mul]; exact Nat.div_lt_of_lt_mul hidx
    set q1 := q % L1; set q2 := q / L1
    have hp : p < 2 * J := Nat.mod_lt idx h2J
    have hq1 : q1 < L1 := Nat.mod_lt q hL1
    have hq2 : q2 < L2 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hq)
    set v := netV9 n + q1
    have hv9 : netV9 n ≤ v := Nat.le_add_right _ _
    have hv10 : v < netV10 n := by have : netV10 n = netV9 n + L1 := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV9 n = q1 := Nat.add_sub_cancel_left _ _
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE9 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE10 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      inL outL (st2Mat J L1 L2 (paramInvOmegaExp n))
      (by rw [rawPred_of_V9 _ _ _ _ _ _ _ hv9 hv10]; simp [inL, outL, J, L1, L2])
      (by rw [(inOut_of_V9 hv9 hv10).1, hsub])
      (by rw [(inOut_of_V9 hv9 hv10).2, hsub])).mp (hsat ⟨v, hv_lt⟩)
    set k := q2 * (2 * J) + p
    have hk_lt : k < 2 * J * L2 := by
      have : q2 * (2 * J) + p < (q2 + 1) * (2 * J) := by
        have : (q2 + 1) * (2 * J) = q2 * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L2]; exact Nat.mul_le_mul_right _ hq2)
    have hstep := hlin k (by simp [outL, hk_lt])
    rw [getD_range_map_nat _ hk_lt] at hstep
    obtain ⟨hdk, hmk⟩ := mul_add_div_mod h2J hp
    have hq_eq : q1 + L1 * q2 = q := mod_add_mul_div q L1
    have he_eq : netE10 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) = netE10 n + idx := by
      rw [hdk, hmk, hq_eq, Nat.add_assoc, div_mul_add_mod idx (2 * J)]
    rw [he_eq] at hstep; rw [hstep]
    unfold mulWiresCraw twoLayerInvSt2
    dsimp only
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := hm
    rw [getD_range_map_nat _ hm']
    have hloc_lt : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he9_eq : netE9 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE9 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    rw [he9_eq, hE9_val _ hloc_lt]
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [hd1, hm1, hd2, hm2]
  have hE11_val : ∀ tk < 2 * n, wireAt n x (netE11 n + tk) = mulWiresZ n h w tk := by
    intro tk htk
    set v := netV11 n + tk
    have hv11 : netV11 n ≤ v := Nat.le_add_right _ _
    have hv12 : v < netV12 n := by have : netV12 n = netV11 n + 2 * n := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV11 n = tk := Nat.add_sub_cancel_left _ _
    set ovl := ovlInLocal J L tk
    have hlin := (eval_linear_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x
      (ovl.map (fun k => netE10 n + k)) [netE11 n + tk] (fun _ _ => true)
      (by rw [rawPred_of_V11 _ _ _ _ _ _ _ hv11 hv12, hsub]; simp [ovl, J, L])
      (by rw [(inOut_of_V11 hv11 hv12).1, hsub])
      (by rw [(inOut_of_V11 hv11 hv12).2, hsub])).mp (hsat ⟨v, hv_lt⟩) 0 (by simp)
    simp only [List.getD_cons_zero] at hlin
    rw [hlin, ← ovlInLocal_parity n h w tk (f := fun k => wireAt n x (netE10 n + k)) hE10_val]
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < ovl.length := by simpa [ovl, J, L] using hi
    rw [getD_map_nat ovl _ hi']
  have hsyn : ∀ k : Fin n,
      (decodeIfaceVec n w).1 k + twoLayerCycMul n h (decodeIfaceVec n w).2 k = s k := by
    intro k
    set v := netV12 n + k.val
    have hv12 : netV12 n ≤ v := Nat.le_add_right _ _
    have hv13 : v < netV13 n := by have : netV13 n = netV12 n + n := rfl; omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV12 n = k.val := Nat.add_sub_cancel_left _ _
    have hev := (eval_V12 mode n h s t0 t1 pre ⟨v, hv_lt⟩ x hv12 hv13).mp (hsat ⟨v, hv_lt⟩)
    have hdite : (if hlt : k.val < n then zmod2ToBool (s ⟨k.val, hlt⟩) else false) = zmod2ToBool (s k) :=
      dite_pos k.isLt
    rw [hsub, hdite,
        (hcopy k.val (by omega)).1,
        hE11_val k.val (by omega),
        show netE11 n + k.val + n = netE11 n + (k.val + n) by omega,
        hE11_val (k.val + n) (by omega)] at hev
    have hb_eq := congrArg boolToZMod2 hev
    rw [boolToZMod2_zmod2ToBool, boolToZMod2_bne, boolToZMod2_bne, add_assoc,
        ← boolToZMod2_bne] at hb_eq
    have he1_fn : (fun idx => if hlt : idx < n then zmod2ToBool ((decodeIfaceVec n w).2 ⟨idx, hlt⟩) else false) =
        e1Bit n w := by
      funext idx
      unfold e1Bit decodeIfaceVec
      dsimp only
      split_ifs with hlt
      · exact zmod2ToBool_boolToZMod2 _
      · rfl
    have hcyc : twoLayerCycMul n h (decodeIfaceVec n w).2 k =
        boolToZMod2 (bne (mulWiresZ n h w k.val) (mulWiresZ n h w (k.val + n))) := by
      unfold twoLayerCycMul mulWiresZ hBit
      dsimp only
      rw [he1_fn]
    rw [← hcyc] at hb_eq
    exact hb_eq
  refine ⟨hpre, ?_, hsyn⟩
  intro e he12
  by_cases he1 : e < netE1 n
  · rw [rawExtWire_of_B0 h t0 w he1, hE0_val e he1]
  by_cases he2 : e < netE2 n
  · rw [rawExtWire_of_B1 h t0 w (by omega) he2]
    have he_eq : e = netE1 n + (e - netE1 n) := by omega
    conv_lhs => rw [he_eq]
    exact (hcopy (e - netE1 n) (by have : netE2 n = 4 * n := rfl; change e - 2 * n < 2 * n; omega)).1
  by_cases he3 : e < netE3 n
  · rw [rawExtWire_of_B2 h t0 w (by omega) he3]
    have he_eq : e = netE2 n + (e - netE2 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE2_val (e - netE2 n) (by have : netE3 n = 4 * n + 2 * treeM n := rfl; have : netE2 n = 4 * n := rfl; omega)
  by_cases he4 : e < netE4 n
  · rw [rawExtWire_of_B3 h t0 w (by omega) he4]
    have he_eq : e = netE3 n + (e - netE3 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE3_val (e - netE3 n) (by have : netE4 n = netE3 n + n := rfl; omega)
  by_cases he5 : e < netE5 n
  · rw [rawExtWire_of_B4 h t0 w (by omega) he5]
    have he_eq : e = netE4 n + (e - netE4 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE4_val (e - netE4 n) (by have : netE5 n = netE4 n + 2 * J * L := rfl; omega)
  by_cases he6 : e < netE6 n
  · rw [rawExtWire_of_B5 h t0 w (by omega) he6]
    have he_eq : e = netE5 n + (e - netE5 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE5_val (e - netE5 n) (by have : netE6 n = netE5 n + 2 * J * L := rfl; omega)
  by_cases he7 : e < netE7 n
  · rw [rawExtWire_of_B6 h t0 w (by omega) he7]
    have he_eq : e = netE6 n + (e - netE6 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE6_val (e - netE6 n) (by have : netE7 n = netE6 n + 2 * J * L := rfl; omega)
  by_cases he8 : e < netE8 n
  · rw [rawExtWire_of_B7 h t0 w (by omega) he8]
    have he_eq : e = netE7 n + (e - netE7 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE7_val (e - netE7 n) (by have : netE8 n = netE7 n + 2 * J * L := rfl; omega)
  by_cases he9 : e < netE9 n
  · rw [rawExtWire_of_B8 h t0 w (by omega) he9]
    have he_eq : e = netE8 n + (e - netE8 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE8_val (e - netE8 n) (by have : netE9 n = netE8 n + 2 * J * L := rfl; omega)
  by_cases he10 : e < netE10 n
  · rw [rawExtWire_of_B9 h t0 w (by omega) he10]
    have he_eq : e = netE9 n + (e - netE9 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE9_val (e - netE9 n) (by have : netE10 n = netE9 n + 2 * J * L := rfl; omega)
  by_cases he11 : e < netE11 n
  · rw [rawExtWire_of_B10 h t0 w (by omega) he11]
    have he_eq : e = netE10 n + (e - netE10 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE10_val (e - netE10 n) (by have : netE11 n = netE10 n + 2 * J * L := rfl; omega)
  · rw [rawExtWire_of_B11 h t0 w (by omega) he12]
    have he_eq : e = netE11 n + (e - netE11 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE11_val (e - netE11 n) (by have : netE12 n = netE11 n + 2 * n := rfl; omega)

/-- Forward propagation Stage B: adder tree `E12`, borrow chain `E13`, and `ModeWeightCond`. -/
lemma sat_imp_tree_and_cmp {mode : ℕ} (hmode : mode ≤ 2) (n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre : List Bool) (x : Fin (netEdgeCount n) → Bool)
    (hsat : ∀ v : Fin (netVertCount n), vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true)
    (w : Fin (2 * n) → Bool)
    (hE2 : ∀ leaf < 2 * treeM n, wireAt n x (netE2 n + leaf) = padLeaves n w leaf) :
    (∀ e, netE12 n ≤ e → e < netEdgeCount n → wireAt n x e = rawExtWire mode n h t0 w e) ∧
    ModeWeightCond mode (QCSD_wt (decodeIfaceVec n w).1) (QCSD_wt (decodeIfaceVec n w).2) t0 t1 := by
  set r := treeLog n + 1
  set W := treeLog n + 2
  have hr2 : 2 ≤ r := by have := one_le_treeLog n; dsimp [r]; omega
  rcases netV_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15_le, hv16_le, hv17_lt, hv18_lt⟩
  rcases netE_chain n with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he12_le, he13_lt⟩
  have hV16 : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
  have hV17 : netV17 n = netV16 n + 1 := rfl
  have hV18 : netV18 n = netV17 n + W := rfl
  have hV19 : netVertCount n = netV18 n + 1 := rfl
  have hE13 : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl
  have hE14 : netEdgeCount n = netE13 n + (W + 1) := rfl
  have htree_ind : ∀ j, 1 ≤ j → j ≤ r → ∀ node < 2 ^ (r - j), ∀ wi < 2 * j + 1,
      wireAt n x (netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + wi)) =
        treeWireVal n w (treeEdgeOff r j + node * (2 * j + 1) + wi) := by
    intro j
    induction j with
    | zero => intro hj1; omega
    | succ m ih =>
      intro _ hjr node hnode
      set j := m + 1
      have hj1_pos : 1 ≤ j := Nat.succ_pos m
      set A := treeLevelBits (2 * treeM n) (padLeaves n w) m (2 * node)
      set B := treeLevelBits (2 * treeM n) (padLeaves n w) m (2 * node + 1)
      have hAB : ∀ b < j,
          wireAt n x (if j = 1 then netE2 n + 2 * node
                      else netE12 n + treeEdgeOff r m + (2 * node) * (2 * m + 1) + sumWireLoc m b) = A b ∧
          wireAt n x (if j = 1 then netE2 n + 2 * node + 1
                      else netE12 n + treeEdgeOff r m + (2 * node + 1) * (2 * m + 1) + sumWireLoc m b) = B b := by
        intro b hb
        by_cases hj1 : j = 1
        · have hm0 : m = 0 := by omega
          have hb0 : b = 0 := by omega
          have hnode_M : node < treeM n := by
            have hr1 : r - 1 = treeLog n := rfl
            simpa [hj1, hr1, treeM] using hnode
          simp only [hj1, ↓reduceIte, hb0]
          have h2n0 : 2 * node < 2 * treeM n := by omega
          have h2n1 : 2 * node + 1 < 2 * treeM n := by omega
          have h1_eq : netE2 n + 2 * node + 1 = netE2 n + (2 * node + 1) := by omega
          rw [hE2 (2 * node) h2n0, h1_eq, hE2 (2 * node + 1) h2n1]
          dsimp [A, B]; rw [hm0]
          simp [treeLevelBits, h2n0, h2n1]
        · simp only [hj1, ↓reduceIte]
          have hm1 : 1 ≤ m := by omega
          have hmr : m ≤ r := by omega
          have hbm : b ≤ m := by omega
          have hexp : r - m = (r - j) + 1 := by omega
          have hc0 : 2 * node < 2 ^ (r - m) := by rw [hexp, pow_succ']; omega
          have hc1 : 2 * node + 1 < 2 ^ (r - m) := by rw [hexp, pow_succ']; omega
          have hsw : sumWireLoc m b < 2 * m + 1 := sumWireLoc_lt hbm
          have heL : netE12 n + treeEdgeOff r m + (2 * node) * (2 * m + 1) + sumWireLoc m b =
              netE12 n + (treeEdgeOff r m + (2 * node) * (2 * m + 1) + sumWireLoc m b) := by omega
          have heR : netE12 n + treeEdgeOff r m + (2 * node + 1) * (2 * m + 1) + sumWireLoc m b =
              netE12 n + (treeEdgeOff r m + (2 * node + 1) * (2 * m + 1) + sumWireLoc m b) := by omega
          rw [heL, ih hm1 hmr (2 * node) hc0 _ hsw, treeWireVal_sumWireLoc n w hm1 hmr hc0 hbm,
              heR, ih hm1 hmr (2 * node + 1) hc1 _ hsw, treeWireVal_sumWireLoc n w hm1 hmr hc1 hbm]
          exact ⟨rfl, rfl⟩
      have hcarry : ∀ b ≤ j,
          wireAt n x (netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * b)) = rippleCarry A B b := by
        intro b
        induction b with
        | zero =>
          intro _
          have hlocV := encodeTreeVert_lt (r := r) (j := j) (node := node) (u := 0)
            hj1_pos hjr hnode (by omega)
          set v := netV15 n + (treeVertOff r j + node * (j + 1) + 0)
          have hv15 : netV15 n ≤ v := Nat.le_add_right _ _
          have hv16 : v < netV16 n := by rw [hV16]; exact Nat.add_lt_add_left hlocV _
          have hv_lt : v < netVertCount n := by omega
          have hdec : decodeTreeVert r (v - netV15 n) = (j, node, 0) := by
            have hv_sub : v - netV15 n = treeVertOff r j + node * (j + 1) + 0 :=
              Nat.add_sub_cancel_left _ _
            rw [hv_sub]
            exact decodeTreeVert_encode (r := r) (j := j) (node := node) (u := 0)
              hj1_pos hjr hnode (by omega)
          have hexp : expectedInc n v = [netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 0)] := by
            unfold expectedInc
            rw [inEdges_of_V15 hv15 hv16 hdec, outEdges_of_V15 hv15 hv16 hdec]
            dsimp only; simp only [↓reduceIte, List.nil_append, List.cons.injEq, and_true]
            dsimp [r]; omega
          have hpred : rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
            rw [rawPred_of_V15 _ _ _ _ _ _ _ hv15 hv16 hdec]; simp
          exact (eval_pin_vertex mode n h s t0 t1 pre ⟨v, hv_lt⟩ x _ (some false) hpred hexp).mp
            (hsat ⟨v, hv_lt⟩)
        | succ b' ihb =>
          intro hb_succ
          have hb_lt : b' < j := by omega
          have hcin := ihb (by omega)
          have hlocV := encodeTreeVert_lt (r := r) (j := j) (node := node) (u := b' + 1)
            hj1_pos hjr hnode (by omega)
          set v := netV15 n + (treeVertOff r j + node * (j + 1) + (b' + 1))
          have hv15 : netV15 n ≤ v := Nat.le_add_right _ _
          have hv16 : v < netV16 n := by rw [hV16]; exact Nat.add_lt_add_left hlocV _
          have hv_lt : v < netVertCount n := by omega
          have hdec : decodeTreeVert r (v - netV15 n) = (j, node, b' + 1) := by
            dsimp [v]; rw [Nat.add_sub_cancel_left]
            exact decodeTreeVert_encode hj1_pos hjr hnode (by omega)
          have hfa := (eval_V15_fa mode n h s t0 t1 pre ⟨v, hv_lt⟩ x hv15 hv16 hdec (by omega)).mp
            (hsat ⟨v, hv_lt⟩)
          have hcout := hfa.2.1
          have hsub1 : b' + 1 - 1 = b' := rfl
          have hj_sub : j - 1 = m := rfl
          rw [hsub1, hj_sub] at hcout
          have hcin_eq : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b' =
              netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * b') := by dsimp [r]; omega
          have hcout_eq : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b' + 2 =
              netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * (b' + 1)) := by dsimp [r]; omega
          rw [hcout_eq, hcin_eq, (hAB b' hb_lt).1, (hAB b' hb_lt).2, hcin] at hcout
          exact hcout
      intro wi hwi
      rcases (show wi % 2 = 0 ∨ wi % 2 = 1 by omega) with heven | hodd
      · set b := wi / 2
        have hwi_eq : wi = 2 * b := by have := Nat.div_add_mod wi 2; omega
        have hb_le : b ≤ j := by omega
        rw [hwi_eq, hcarry b hb_le, treeWireVal_even n w hj1_pos hjr hnode hb_le]
        rfl
      · set b := wi / 2
        have hwi_eq : wi = 2 * b + 1 := by have := Nat.div_add_mod wi 2; omega
        have hb_lt : b < j := by omega
        have hlocV := encodeTreeVert_lt (r := r) (j := j) (node := node) (u := b + 1)
          hj1_pos hjr hnode (by omega)
        set v := netV15 n + (treeVertOff r j + node * (j + 1) + (b + 1))
        have hv15 : netV15 n ≤ v := Nat.le_add_right _ _
        have hv16 : v < netV16 n := by rw [hV16]; exact Nat.add_lt_add_left hlocV _
        have hv_lt : v < netVertCount n := by omega
        have hdec : decodeTreeVert r (v - netV15 n) = (j, node, b + 1) := by
          dsimp [v]; rw [Nat.add_sub_cancel_left]
          exact decodeTreeVert_encode hj1_pos hjr hnode (by omega)
        have hfa := (eval_V15_fa mode n h s t0 t1 pre ⟨v, hv_lt⟩ x hv15 hv16 hdec (by omega)).mp
          (hsat ⟨v, hv_lt⟩)
        have hsum := hfa.1
        have hsub1 : b + 1 - 1 = b := rfl
        have hj_sub : j - 1 = m := rfl
        rw [hsub1, hj_sub] at hsum
        have hcin_eq : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b =
            netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * b) := by dsimp [r]; omega
        have hsum_eq : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b + 1 =
            netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + (2 * b + 1)) := by dsimp [r]; omega
        rw [hsum_eq, hcin_eq, (hAB b hb_lt).1, (hAB b hb_lt).2, hcarry b (by omega)] at hsum
        rw [hwi_eq, hsum, treeWireVal_odd n w hj1_pos hjr hnode hb_lt]
        rfl
  have hE12_val : ∀ locE < treeEdgeOff r (r + 1),
      wireAt n x (netE12 n + locE) = treeWireVal n w locE := by
    intro locE hlocE
    obtain ⟨hj1, hjr, hnode, hwi, hlocE_eq⟩ := decodeTreeEdge_spec hlocE
    rw [hlocE_eq]
    exact htree_ind _ hj1 hjr _ hnode _ hwi
  set topSum := treeLevelBits (2 * treeM n) (padLeaves n w) r 0
  have htop_wire : ∀ b < W,
      wireAt n x (netE12 n + treeEdgeOff r r + sumWireLoc r b) = topSum b := by
    intro b hb
    have hb_le : b ≤ r := by dsimp [r, W] at hb ⊢; omega
    have hsw : sumWireLoc r b < 2 * r + 1 := sumWireLoc_lt hb_le
    have hlocE : treeEdgeOff r r + 0 * (2 * r + 1) + sumWireLoc r b < treeEdgeOff r (r + 1) :=
      encodeTreeEdge_lt (by omega) le_rfl (by simp) hsw
    have he_eq : netE12 n + treeEdgeOff r r + sumWireLoc r b =
        netE12 n + (treeEdgeOff r r + 0 * (2 * r + 1) + sumWireLoc r b) := by omega
    rw [he_eq, hE12_val _ hlocE, treeWireVal_sumWireLoc n w (by omega) le_rfl (by simp) hb_le]
  have hb0_zero : wireAt n x (netE13 n) = false := by
    have hv16_lt17 : netV16 n < netV17 n := by omega
    have hv_lt : netV16 n < netVertCount n := by omega
    have hexp : expectedInc n (netV16 n) = [netE13 n] := by
      unfold expectedInc
      rw [(inOut_of_V16 le_rfl hv16_lt17).1, (inOut_of_V16 le_rfl hv16_lt17).2, List.nil_append]
    exact (eval_pin_vertex mode n h s t0 t1 pre ⟨netV16 n, hv_lt⟩ x (netE13 n) (some false)
      (rawPred_of_V16 _ _ _ _ _ _ _ le_rfl hv16_lt17) hexp).mp (hsat ⟨netV16 n, hv_lt⟩)
  have hcmp_step : ∀ b < W,
      (if mode = 0 then
         t0 < 2 ^ W ∧ topSum b = t0.testBit b ∧ wireAt n x (netE13 n + b + 1) = false
       else if mode = 1 then
         wireAt n x (netE13 n + b + 1) =
           (if t0.testBit b then (topSum b && wireAt n x (netE13 n + b))
            else (topSum b || wireAt n x (netE13 n + b)))
       else
         wireAt n x (netE13 n + b + 1) = false) := by
    intro b hb
    set v := netV17 n + b
    have hv17 : netV17 n ≤ v := Nat.le_add_right _ _
    have hv18 : v < netV18 n := by omega
    have hv_lt : v < netVertCount n := by omega
    have hsub : v - netV17 n = b := Nat.add_sub_cancel_left _ _
    have hs := (eval_V17 mode n h s t0 t1 pre ⟨v, hv_lt⟩ x hv17 hv18).mp (hsat ⟨v, hv_lt⟩)
    dsimp only at hs
    rw [hsub, show treeEdgeOff (treeLog n + 1) (treeLog n + 1) = treeEdgeOff r r from rfl,
        show sumWireLoc (treeLog n + 1) b = sumWireLoc r b from rfl,
        htop_wire b hb] at hs
    exact hs
  have hE13_and_mode :
      (∀ k < W + 1, wireAt n x (netE13 n + k) = borrowWireVal mode n t0 w k) ∧
      ModeWeightCond mode (QCSD_wt (decodeIfaceVec n w).1) (QCSD_wt (decodeIfaceVec n w).2) t0 t1 := by
    by_cases hm0 : mode = 0
    · subst hm0
      simp only [ModeWeightCond, ↓reduceIte]
      have h0 := hcmp_step 0 (by dsimp [W]; omega)
      simp only [↓reduceIte] at h0
      refine ⟨?_, ?_⟩
      · intro k hk
        unfold borrowWireVal; simp only [show ¬(0 = 1) by decide, ↓reduceIte]
        cases k with
        | zero => simpa using hb0_zero
        | succ b =>
          have hb := hcmp_step b (by omega)
          simp only [↓reduceIte] at hb
          have heq : netE13 n + (b + 1) = netE13 n + b + 1 := by omega
          rw [heq]; exact hb.2.2
      · rw [← padLeaves_wt_sum n w]
        change bitsVal W topSum = t0
        rw [bitsVal_eq_iff_testBit]
        refine ⟨h0.1, fun b hb => ?_⟩
        have hstep := hcmp_step b hb
        simp only [↓reduceIte] at hstep
        exact hstep.2.1
    · by_cases hm1 : mode = 1
      · subst hm1
        simp only [ModeWeightCond, show ¬(1 = 0) by decide, ↓reduceIte]
        have hbor : ∀ k ≤ W, wireAt n x (netE13 n + k) = leBorrow topSum t0 k := by
          intro k
          induction k with
          | zero => intro _; simpa [leBorrow] using hb0_zero
          | succ b ihk =>
            intro hbk
            have hstep := hcmp_step b (by omega)
            simp only [show ¬(1 = 0) by decide, ↓reduceIte] at hstep
            have heq : netE13 n + (b + 1) = netE13 n + b + 1 := by omega
            rw [heq, hstep, ihk (by omega)]
            rfl
        refine ⟨?_, ?_⟩
        · intro k hk
          unfold borrowWireVal; simp only [↓reduceIte]
          exact hbor k (by omega)
        · rw [← padLeaves_wt_sum n w]
          change bitsVal W topSum ≤ t0
          rw [bitsVal_le_iff_leBorrow W topSum t0]
          have hv18_lt : netV18 n < netVertCount n := by omega
          have htop_v := (eval_V18 1 n h s t0 t1 pre ⟨netV18 n, hv18_lt⟩ x le_rfl).mp
            (hsat ⟨netV18 n, hv18_lt⟩)
          by_cases ht_lt : t0 < 2 ^ W
          · simp only [ht_lt, ↓reduceIte]
            have hnc : ¬(1 = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2))) := by dsimp [W] at ht_lt; omega
            rw [ite_neg hnc] at htop_v
            rw [← hbor W le_rfl]
            exact htop_v
          · simp [ht_lt]
      · have hm2 : mode = 2 := by omega
        subst hm2
        simp only [ModeWeightCond, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · intro k hk
          unfold borrowWireVal; simp only [show ¬(2 = 1) by decide, ↓reduceIte]
          cases k with
          | zero => simpa using hb0_zero
          | succ b =>
            have hb := hcmp_step b (by omega)
            simp only [show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hb
            have heq : netE13 n + (b + 1) = netE13 n + b + 1 := by omega
            rw [heq]; exact hb
        · have hsep_step : ∀ b < r,
              t0 < 2 ^ r ∧ t1 < 2 ^ r ∧
              treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 0 b = t0.testBit b ∧
              treeLevelBits (2 * treeM n) (padLeaves n w) (treeLog n) 1 b = t1.testBit b := by
            intro b hb
            have hlocV := encodeTreeVert_lt (r := r) (j := r) (node := 0) (u := b + 1)
              (by omega) le_rfl (by simp) (by omega)
            set v := netV15 n + (treeVertOff r r + 0 * (r + 1) + (b + 1))
            have hv15 : netV15 n ≤ v := Nat.le_add_right _ _
            have hv16 : v < netV16 n := by rw [hV16]; exact Nat.add_lt_add_left hlocV _
            have hv_lt : v < netVertCount n := by omega
            have hdec : decodeTreeVert r (v - netV15 n) = (r, 0, b + 1) := by
              dsimp [v]; rw [Nat.add_sub_cancel_left]
              exact decodeTreeVert_encode (by omega) le_rfl (by simp) (by omega)
            have hfa := (eval_V15_fa 2 n h s t0 t1 pre ⟨v, hv_lt⟩ x hv15 hv16 hdec (by omega)).mp
              (hsat ⟨v, hv_lt⟩)
            have hpins := hfa.2.2 ⟨rfl, rfl⟩
            have hnr1 : ¬(r = 1) := by omega
            have hr_sub : r - 1 = treeLog n := rfl
            have hb_sub : b + 1 - 1 = b := rfl
            simp only [hnr1, ↓reduceIte, hr_sub, hb_sub] at hpins
            set r1 := treeLog n
            have hr1_ge : 1 ≤ r1 := one_le_treeLog n
            have hr1_le : r1 ≤ r := by dsimp [r1, r]; omega
            have hb_le : b ≤ r1 := by dsimp [r1, r] at hb ⊢; omega
            have hsw : sumWireLoc r1 b < 2 * r1 + 1 := sumWireLoc_lt hb_le
            have hc0 : 0 < 2 ^ (r - r1) := by dsimp [r1, r]; rw [Nat.add_sub_cancel_left]; decide
            have hc1 : 1 < 2 ^ (r - r1) := by dsimp [r1, r]; rw [Nat.add_sub_cancel_left]; decide
            have hloc0 := encodeTreeEdge_lt hr1_ge hr1_le hc0 hsw
            have hloc1 := encodeTreeEdge_lt hr1_ge hr1_le hc1 hsw
            have he0_eq : netE12 n + treeEdgeOff (treeLog n + 1) r1 + (2 * 0) * (2 * r1 + 1) + sumWireLoc r1 b =
                netE12 n + (treeEdgeOff r r1 + 0 * (2 * r1 + 1) + sumWireLoc r1 b) := by dsimp [r]; omega
            have he1_eq : netE12 n + treeEdgeOff (treeLog n + 1) r1 + (2 * 0 + 1) * (2 * r1 + 1) + sumWireLoc r1 b =
                netE12 n + (treeEdgeOff r r1 + 1 * (2 * r1 + 1) + sumWireLoc r1 b) := by dsimp [r]; omega
            rw [he0_eq, hE12_val _ hloc0, treeWireVal_sumWireLoc n w hr1_ge hr1_le hc0 hb_le,
                he1_eq, hE12_val _ hloc1, treeWireVal_sumWireLoc n w hr1_ge hr1_le hc1 hb_le] at hpins
            exact hpins
          have h0 := hsep_step 0 (by omega)
          rw [← padLeaves_wt0 n w, ← padLeaves_wt1 n w]
          change bitsVal r _ = t0 ∧ bitsVal r _ = t1
          rw [bitsVal_eq_iff_testBit, bitsVal_eq_iff_testBit]
          exact ⟨⟨h0.1, fun b hb => (hsep_step b hb).2.2.1⟩,
                 ⟨h0.2.1, fun b hb => (hsep_step b hb).2.2.2⟩⟩
  refine ⟨?_, hE13_and_mode.2⟩
  intro e he12 he_lt
  by_cases he13 : e < netE13 n
  · rw [rawExtWire_of_B12 h t0 w he12 he13]
    have he_eq : e = netE12 n + (e - netE12 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE12_val (e - netE12 n) (by omega)
  · rw [rawExtWire_of_B13 h t0 w (by omega)]
    have he_eq : e = netE13 n + (e - netE13 n) := by omega
    conv_lhs => rw [he_eq]
    exact hE13_and_mode.1 (e - netE13 n) (by omega)

/-- Backward verification Part A: `extWire` satisfies vertices `V0..V11`. -/
lemma extWire_sat_0_11 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (w : Fin (2 * n) → Bool)
    (hpre : ∀ i : Fin (2 * n), i.val < pre.length → w i = pre.getD i.val false)
    (v : Fin (netVertCount n)) (hv12 : v.val < netV12 n) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v (extWire mode n h t0 w) = true := by
  set x := extWire mode n h t0 w
  set J := paramJ n; set L := paramL n; set L1 := paramL1 n; set L2 := paramL2 n
  have h2J : 0 < 2 * J := by have := paramJ_pos n; omega
  have hL1 : 0 < L1 := one_le_paramL1 n
  have hL2 : 0 < L2 := one_le_paramL2 n
  have hL_mul : L = L1 * L2 := paramL_eq_mul n
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netE_chain n with
    ⟨he0_le, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hB0 : ∀ i (hi : i < 2 * n), wireAt n x i = w ⟨i, hi⟩ := fun i hi => by
    rw [wireAt_extWire h t0 w (lt_of_lt_of_le hi (netE1_le_netEdgeCount n)), rawExtWire_of_B0 h t0 w hi]
  have hB1 : ∀ i (hi : i < 2 * n), wireAt n x (netE1 n + i) = w ⟨i, hi⟩ := fun i hi => by
    have he : netE1 n + i < netE2 n := by change 2 * n + i < 4 * n; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B1 h t0 w (Nat.le_add_right _ _) he]
    apply congrArg w; apply Fin.ext; dsimp only; exact Nat.add_sub_cancel_left _ _
  have hB2 : ∀ leaf < 2 * treeM n, wireAt n x (netE2 n + leaf) = padLeaves n w leaf := fun leaf hl => by
    have he : netE2 n + leaf < netE3 n := by
      have : netE2 n = 4 * n := rfl; have : netE3 n = 4 * n + 2 * treeM n := rfl; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B2 h t0 w (Nat.le_add_right _ _) he,
        Nat.add_sub_cancel_left]
  have hB3 : ∀ idx < n, wireAt n x (netE3 n + idx) = hBit n h idx := fun idx hi => by
    have he : netE3 n + idx < netE4 n := by have : netE4 n = netE3 n + n := rfl; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B3 h t0 w (Nat.le_add_right _ _) he,
        Nat.add_sub_cancel_left]
  have hB4 : ∀ idx < 2 * J * L,
      wireAt n x (netE4 n + idx) = mulWiresYa n h ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE4 n + idx < netE5 n := by have : netE5 n = netE4 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B4 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB5 : ∀ idx < 2 * J * L,
      wireAt n x (netE5 n + idx) = mulWiresFa n h (idx / (2 * J)) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE5 n + idx < netE6 n := by have : netE6 n = netE5 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B5 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB6 : ∀ idx < 2 * J * L,
      wireAt n x (netE6 n + idx) = mulWiresYb n w ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE6 n + idx < netE7 n := by have : netE7 n = netE6 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B6 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB7 : ∀ idx < 2 * J * L,
      wireAt n x (netE7 n + idx) = mulWiresFb n w (idx / (2 * J)) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE7 n + idx < netE8 n := by have : netE8 n = netE7 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B7 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB8 : ∀ idx < 2 * J * L,
      wireAt n x (netE8 n + idx) = mulWiresFc n h w (idx / (2 * J)) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE8 n + idx < netE9 n := by have : netE9 n = netE8 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B8 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB9 : ∀ idx < 2 * J * L,
      wireAt n x (netE9 n + idx) = mulWiresYc n h w ((idx / (2 * J)) / L1) ((idx / (2 * J)) % L1) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE9 n + idx < netE10 n := by have : netE10 n = netE9 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B9 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB10 : ∀ idx < 2 * J * L,
      wireAt n x (netE10 n + idx) = mulWiresCraw n h w (idx / (2 * J)) (idx % (2 * J)) :=
    fun idx hi => by
      have he : netE10 n + idx < netE11 n := by have : netE11 n = netE10 n + 2 * J * L := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B10 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  have hB11 : ∀ tk < 2 * n, wireAt n x (netE11 n + tk) = mulWiresZ n h w tk :=
    fun tk htk => by
      have he : netE11 n + tk < netE12 n := by have : netE12 n = netE11 n + 2 * n := rfl; omega
      rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B11 h t0 w (Nat.le_add_right _ _) he,
          Nat.add_sub_cancel_left]
  by_cases hv1 : v.val < netV1 n
  · have hexp : expectedInc n v.val = [v.val] := by
      unfold expectedInc; rw [(inOut_of_V0 hv1).1, (inOut_of_V0 hv1).2]; simp [netE0]
    by_cases hlt : v.val < pre.length
    · have hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit (some (pre.getD v.val false)) := by
        rw [rawPred_of_V0 _ _ _ _ _ _ _ hv1, ite_pos hlt]
      rw [eval_pin_vertex mode n h s t0 t1 pre v x v.val _ hpred hexp]
      dsimp only; rw [hB0 v.val hv1]; exact hpre ⟨v.val, hv1⟩ hlt
    · have hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit none := by
        rw [rawPred_of_V0 _ _ _ _ _ _ _ hv1, ite_neg hlt]
      rw [eval_pin_vertex mode n h s t0 t1 pre v x v.val _ hpred hexp]
      trivial
  by_cases hv2 : v.val < netV2 n
  · set i := v.val - netV1 n
    have hi : i < 2 * n := by have : netV2 n = 4 * n := rfl; change v.val - 2 * n < 2 * n; omega
    rw [eval_linear_vertex mode n h s t0 t1 pre v x [netE0 n + i]
      [netE1 n + i, netE2 n + (if i < n then i else treeM n + (i - n))] (fun _ _ => true)
      (rawPred_of_V1 _ _ _ _ _ _ _ (by omega) hv2)
      (inOut_of_V1 (by omega) hv2).1 (inOut_of_V1 (by omega) hv2).2]
    intro k hk
    have htgt : linearMapTarget 1 (fun _ _ => true) (fun m => wireAt n x ([netE0 n + i].getD m 0)) k = w ⟨i, hi⟩ := by
      change bne false (wireAt n x (0 + i)) = _; rw [Nat.zero_add, hB0 i hi]; cases w ⟨i, hi⟩ <;> rfl
    simp only [List.length_singleton]
    rw [htgt]
    rcases (show k = 0 ∨ k = 1 by simp at hk; omega) with rfl | rfl
    · simp only [List.getD_cons_zero]; exact hB1 i hi
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hin : i < n
      · simp only [hin, ↓reduceIte]; rw [hB2 i (by omega)]; simp [padLeaves, hin]
      · simp only [hin, ↓reduceIte]
        rw [hB2 (treeM n + (i - n)) (by omega)]
        unfold padLeaves
        have hn1 : ¬(treeM n + (i - n) < n) := by omega
        have hn2 : ¬(treeM n + (i - n) < treeM n) := by omega
        have hy : treeM n + (i - n) < treeM n + n := by omega
        simp only [hn1, hn2, hy, ↓reduceDIte]
        apply congrArg w; apply Fin.ext; dsimp only; omega
  by_cases hv3 : v.val < netV3 n
  · set idx := v.val - netV2 n
    have hidx : idx < n := by have : netV2 n = 4 * n := rfl; have : netV3 n = 5 * n := rfl; omega
    have hexp : expectedInc n v.val = [netE3 n + idx] := by
      unfold expectedInc; rw [(inOut_of_V2 (by omega) hv3).1, (inOut_of_V2 (by omega) hv3).2]; rfl
    have hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit (some (hBit n h idx)) := by
      rw [rawPred_of_V2 _ _ _ _ _ _ _ (by omega) hv3]; rfl
    rw [eval_pin_vertex mode n h s t0 t1 pre v x (netE3 n + idx) (some (hBit n h idx)) hpred hexp]
    exact hB3 idx hidx
  by_cases hv4 : v.val < netV4 n
  · set j2 := v.val - netV3 n
    have hj2 : j2 < L2 := by have : netV4 n = netV3 n + L2 := rfl; omega
    set inList := fwdSt1InIndices n J L2 j2
    set outL := (List.range (2 * J * L1)).map
      (fun k => netE4 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x (inList.map (fun m => netE3 n + m)) outL
      (fwdSt1Mat J L1 (paramOmegaExp n) inList)
      (by rw [rawPred_of_V3 _ _ _ _ _ _ _ (by omega) hv4]; simp [inList, outL, J, L1, L2]; rfl)
      (inOut_of_V3 (by omega) hv4).1 (inOut_of_V3 (by omega) hv4).2]
    intro k hk
    have hk' : k < 2 * J * L1 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_lt : (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_contig_lt hj2 hk'
    have he_eq : netE4 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) =
        netE4 n + ((j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB4 _ hloc_lt]
    have hq1 : k / (2 * J) < L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk')
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod (W := L1) (q := j2) (p := k / (2 * J)) hL1 hq1
    rw [hd1, hm1, hd2, hm2]
    unfold mulWiresYa twoLayerFwdSt1; dsimp only
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < inList.length := by simpa [inList, J, L2] using hi
    rw [getD_map_nat inList _ hi', hB3 _ (fwdSt1InIndices_getD_lt hi')]
  by_cases hv5 : v.val < netV5 n
  · set q1 := v.val - netV4 n
    have hq1 : q1 < L1 := by have : netV5 n = netV4 n + L1 := rfl; omega
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE4 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE5 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x inL outL (st2Mat J L1 L2 (paramOmegaExp n))
      (by rw [rawPred_of_V4 _ _ _ _ _ _ _ (by omega) hv5]; simp [inL, outL, J, L1, L2])
      (inOut_of_V4 (by omega) hv5).1 (inOut_of_V4 (by omega) hv5).2]
    intro k hk
    have hk' : k < 2 * J * L2 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_out : (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) < 2 * J * L := by
      have hc : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
      rw [hc, hL_mul]; exact affine_stride_lt h2J hq1 hk'
    have he_eq : netE5 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) =
        netE5 n + ((q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB5 _ hloc_out]
    obtain ⟨hd_out, hm_out⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    rw [hd_out, hm_out]
    unfold mulWiresFa twoLayerFwdSt2; dsimp only
    have hc_q : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
    obtain ⟨hd_q, hm_q⟩ := mul_add_div_mod (W := L1) (q := k / (2 * J)) (p := q1) hL1 hq1
    rw [hc_q, hd_q, hm_q]
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := by simpa [inL, J, L2] using hm
    rw [getD_range_map_nat _ hm']
    have hloc_in : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he4_eq : netE4 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE4 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [he4_eq, hB4 _ hloc_in, hd1, hm1, hd2, hm2]
  by_cases hv6 : v.val < netV6 n
  · set j2 := v.val - netV5 n
    have hV6_eq : netV6 n = netV5 n + L2 := by unfold netV5 netV6; dsimp only [L2]; ring
    have hj2 : j2 < L2 := by omega
    set inList := fwdSt1InIndices n J L2 j2
    set outL := (List.range (2 * J * L1)).map
      (fun k => netE6 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x (inList.map (fun m => netE1 n + n + m)) outL
      (fwdSt1Mat J L1 (paramOmegaExp n) inList)
      (by rw [rawPred_of_V5 _ _ _ _ _ _ _ (by omega) hv6]; simp [inList, outL, J, L1, L2]; rfl)
      (inOut_of_V5 (by omega) hv6).1 (inOut_of_V5 (by omega) hv6).2]
    intro k hk
    have hk' : k < 2 * J * L1 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_lt : (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_contig_lt hj2 hk'
    have he_eq : netE6 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) =
        netE6 n + ((j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB6 _ hloc_lt]
    have hq1 : k / (2 * J) < L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk')
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod (W := L1) (q := j2) (p := k / (2 * J)) hL1 hq1
    rw [hd1, hm1, hd2, hm2]
    unfold mulWiresYb twoLayerFwdSt1; dsimp only
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < inList.length := by simpa [inList, J, L2] using hi
    have hlt_n : inList.getD i 0 < n := fwdSt1InIndices_getD_lt hi'
    rw [getD_map_nat inList _ hi']
    have he1_eq : netE1 n + n + inList.getD i 0 = netE1 n + (n + inList.getD i 0) := by omega
    rw [he1_eq, hB1 (n + inList.getD i 0) (by omega)]
    unfold e1Bit
    rw [dite_pos (fwdSt1InIndices_getD_lt hi')]
  by_cases hv7 : v.val < netV7 n
  · set q1 := v.val - netV6 n
    have hV7_eq : netV7 n = netV6 n + L1 := by unfold netV6 netV7; dsimp only [L1]; ring
    have hq1 : q1 < L1 := by omega
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE6 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE7 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x inL outL (st2Mat J L1 L2 (paramOmegaExp n))
      (by rw [rawPred_of_V6 _ _ _ _ _ _ _ (by omega) hv7]; simp [inL, outL, J, L1, L2])
      (inOut_of_V6 (by omega) hv7).1 (inOut_of_V6 (by omega) hv7).2]
    intro k hk
    have hk' : k < 2 * J * L2 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_out : (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) < 2 * J * L := by
      have hc : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
      rw [hc, hL_mul]; exact affine_stride_lt h2J hq1 hk'
    have he_eq : netE7 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) =
        netE7 n + ((q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB7 _ hloc_out]
    obtain ⟨hd_out, hm_out⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    rw [hd_out, hm_out]
    unfold mulWiresFb twoLayerFwdSt2; dsimp only
    have hc_q : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
    obtain ⟨hd_q, hm_q⟩ := mul_add_div_mod (W := L1) (q := k / (2 * J)) (p := q1) hL1 hq1
    rw [hc_q, hd_q, hm_q]
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := by simpa [inL, J, L2] using hm
    rw [getD_range_map_nat _ hm']
    have hloc_in : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he6_eq : netE6 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE6 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [he6_eq, hB6 _ hloc_in, hd1, hm1, hd2, hm2]
  by_cases hv8 : v.val < netV8 n
  · set q := v.val - netV7 n
    have hq : q < L := by have : netV8 n = netV7 n + L := rfl; omega
    rw [eval_V7 mode n h s t0 t1 pre v x (by omega) hv8]
    intro p hp
    change wireAt n x (netE8 n + q * (2 * J) + p) =
      ringMulBits (paramJ n)
        (fun m => wireAt n x (netE5 n + q * (2 * J) + m))
        (fun m => wireAt n x (netE7 n + q * (2 * J) + m)) p
    have hp' : p < 2 * J := hp
    have hloc : q * (2 * J) + p < 2 * J * L := by
      have : q * (2 * J) + p < (q + 1) * (2 * J) := by
        have : (q + 1) * (2 * J) = q * (2 * J) + 2 * J := by ring
        omega
      exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L]; exact Nat.mul_le_mul_right _ hq)
    have he8_eq : netE8 n + q * (2 * J) + p = netE8 n + (q * (2 * J) + p) := by omega
    obtain ⟨hd_p, hm_p⟩ := mul_add_div_mod h2J hp'
    rw [he8_eq, hB8 _ hloc, hd_p, hm_p]
    unfold mulWiresFc ringMulBits
    apply bilinearMapTarget_congr h2J
    intro m hm
    by_cases hm1 : m < 2 * J
    · have hm1' : m < 2 * paramJ n := hm1
      simp only [hm1', ↓reduceIte]
      have hlt5 : q * (2 * J) + m < 2 * J * L := by
        have : q * (2 * J) + m < (q + 1) * (2 * J) := by
          have : (q + 1) * (2 * J) = q * (2 * J) + 2 * J := by ring
          omega
        exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L]; exact Nat.mul_le_mul_right _ hq)
      have he5_eq : netE5 n + q * (2 * J) + m = netE5 n + (q * (2 * J) + m) := by omega
      obtain ⟨hd, hmd⟩ := mul_add_div_mod h2J hm1
      rw [he5_eq, hB5 _ hlt5, hd, hmd]
    · have hm1' : ¬(m < 2 * paramJ n) := hm1
      simp only [hm1', ↓reduceIte]
      have hsub_m : m - 2 * J < 2 * J := by omega
      have hlt7 : q * (2 * J) + (m - 2 * J) < 2 * J * L := by
        have : q * (2 * J) + (m - 2 * J) < (q + 1) * (2 * J) := by
          have : (q + 1) * (2 * J) = q * (2 * J) + 2 * J := by ring
          omega
        exact lt_of_lt_of_le this (by rw [Nat.mul_comm (2 * J) L]; exact Nat.mul_le_mul_right _ hq)
      have he7_eq : netE7 n + q * (2 * J) + (m - 2 * J) = netE7 n + (q * (2 * J) + (m - 2 * J)) := by omega
      obtain ⟨hd, hmd⟩ := mul_add_div_mod h2J hsub_m
      rw [he7_eq, hB7 _ hlt7, hd, hmd]
  by_cases hv9 : v.val < netV9 n
  · set j2 := v.val - netV8 n
    have hj2 : j2 < L2 := by have : netV9 n = netV8 n + L2 := rfl; omega
    set inL := (List.range (2 * J * L1)).map
      (fun m => netE8 n + (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L1)).map
      (fun m => netE9 n + (j2 * L1 + m / (2 * J)) * (2 * J) + m % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x inL outL
      (fullSt1Mat J L1 L2 (paramInvOmegaExp n) j2)
      (by rw [rawPred_of_V8 _ _ _ _ _ _ _ (by omega) hv9]; simp [inL, outL, J, L1, L2]; rfl)
      (inOut_of_V8 (by omega) hv9).1 (inOut_of_V8 (by omega) hv9).2]
    intro k hk
    have hk' : k < 2 * J * L1 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_out : (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_contig_lt hj2 hk'
    have he_eq : netE9 n + (j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J) =
        netE9 n + ((j2 * L1 + k / (2 * J)) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB9 _ hloc_out]
    have hq1 : k / (2 * J) < L1 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk')
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod (W := L1) (q := j2) (p := k / (2 * J)) hL1 hq1
    rw [hd1, hm1, hd2, hm2]
    unfold mulWiresYc twoLayerInvSt1; dsimp only
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    have hinL_len : inL.length = 2 * paramJ n * paramL1 n := by simp [inL, J, L1]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L1 := by simpa [inL, J, L1] using hm
    rw [getD_range_map_nat _ hm']
    have hloc_in : (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J) < 2 * J * L := by
      have hc : L2 * (m / (2 * J)) = (m / (2 * J)) * L2 := Nat.mul_comm _ _
      rw [hc, hL_mul, Nat.mul_comm L1 L2]; exact affine_stride_lt h2J hj2 hm'
    have he8_eq : netE8 n + (L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J) =
        netE8 n + ((L2 * (m / (2 * J)) + j2) * (2 * J) + m % (2 * J)) := by omega
    obtain ⟨hd_in, hm_in⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    rw [he8_eq, hB8 _ hloc_in, hd_in, hm_in]
  by_cases hv10 : v.val < netV10 n
  · set q1 := v.val - netV9 n
    have hq1 : q1 < L1 := by have : netV10 n = netV9 n + L1 := rfl; omega
    set inL := (List.range (2 * J * L2)).map
      (fun m => netE9 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J))
    set outL := (List.range (2 * J * L2)).map
      (fun m => netE10 n + (q1 + L1 * (m / (2 * J))) * (2 * J) + m % (2 * J))
    rw [eval_linear_vertex mode n h s t0 t1 pre v x inL outL (st2Mat J L1 L2 (paramInvOmegaExp n))
      (by rw [rawPred_of_V9 _ _ _ _ _ _ _ (by omega) hv10]; simp [inL, outL, J, L1, L2])
      (inOut_of_V9 (by omega) hv10).1 (inOut_of_V9 (by omega) hv10).2]
    intro k hk
    have hk' : k < 2 * J * L2 := by simpa [outL] using hk
    rw [getD_range_map_nat _ hk']
    have hloc_out : (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) < 2 * J * L := by
      have hc : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
      rw [hc, hL_mul]; exact affine_stride_lt h2J hq1 hk'
    have he_eq : netE10 n + (q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J) =
        netE10 n + ((q1 + L1 * (k / (2 * J))) * (2 * J) + k % (2 * J)) := by omega
    rw [he_eq, hB10 _ hloc_out]
    obtain ⟨hd_out, hm_out⟩ := mul_add_div_mod h2J (Nat.mod_lt k h2J)
    rw [hd_out, hm_out]
    unfold mulWiresCraw twoLayerInvSt2; dsimp only
    have hc_q : q1 + L1 * (k / (2 * J)) = (k / (2 * J)) * L1 + q1 := by ring
    obtain ⟨hd_q, hm_q⟩ := mul_add_div_mod (W := L1) (q := k / (2 * J)) (p := q1) hL1 hq1
    rw [hc_q, hd_q, hm_q]
    have hk_eq : (k / (2 * J)) * (2 * J) + k % (2 * J) = k := div_mul_add_mod k (2 * J)
    rw [hk_eq]
    have hinL_len : inL.length = 2 * paramJ n * paramL2 n := by simp [inL, J, L2]
    rw [hinL_len]
    apply linearMapTarget_congr
    intro m hm
    have hm' : m < 2 * J * L2 := by simpa [inL, J, L2] using hm
    rw [getD_range_map_nat _ hm']
    have hloc_in : ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) < 2 * J * L := by
      rw [hL_mul]; exact affine_stride_lt h2J hq1 hm'
    have he9_eq : netE9 n + ((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J) =
        netE9 n + (((m / (2 * J)) * L1 + q1) * (2 * J) + m % (2 * J)) := by omega
    obtain ⟨hd1, hm1⟩ := mul_add_div_mod h2J (Nat.mod_lt m h2J)
    obtain ⟨hd2, hm2⟩ := mul_add_div_mod hL1 hq1
    rw [he9_eq, hB9 _ hloc_in, hd1, hm1, hd2, hm2]
  by_cases hv11 : v.val < netV11 n
  · exact eval_V10 mode n h s t0 t1 pre v x (by omega) hv11
  · set tk := v.val - netV11 n
    have htk : tk < 2 * n := by have : netV12 n = netV11 n + 2 * n := rfl; omega
    set ovl := ovlInLocal J L tk
    rw [eval_linear_vertex mode n h s t0 t1 pre v x (ovl.map (fun k => netE10 n + k))
      [netE11 n + tk] (fun _ _ => true)
      (by rw [rawPred_of_V11 _ _ _ _ _ _ _ (by omega) hv12]; simp [ovl, J, L]; rfl)
      (inOut_of_V11 (by omega) hv12).1 (inOut_of_V11 (by omega) hv12).2]
    intro k hk
    have hk0 : k = 0 := by simp at hk; exact hk
    subst hk0
    simp only [List.getD_cons_zero]
    rw [hB11 tk htk, ← ovlInLocal_parity n h w tk (f := fun m => wireAt n x (netE10 n + m)) hB10]
    symm
    simp only [List.length_map]
    apply linearMapTarget_congr
    intro i hi
    have hi' : i < ovl.length := by simpa [ovl, J, L] using hi
    rw [getD_map_nat ovl _ hi']

/-- Backward verification Part B: `extWire` satisfies vertices `V12..V18`. -/
lemma extWire_sat_12_18 {mode : ℕ} (hmode : mode ≤ 2) (n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre : List Bool) (w : Fin (2 * n) → Bool)
    (hval : ValidModeIface mode n h s t0 t1 pre w)
    (v : Fin (netVertCount n)) (hv12 : netV12 n ≤ v.val) :
    vertexSat (buildQCSDNet mode n h s t0 t1 pre) v (extWire mode n h t0 w) = true := by
  set x := extWire mode n h t0 w
  set r := treeLog n + 1
  set W := treeLog n + 2
  have hM1 : n ≤ treeM n := le_treeM n
  rcases netE_chain n with
    ⟨he0_le, he1_le, he2_le, he3_le, he4_le, he5_le, he6_le, he7_le, he8_le, he9_le,
     he10_le, he11_le, he12_le, he13_lt⟩
  have hB1 : ∀ i (hi : i < 2 * n), wireAt n x (netE1 n + i) = w ⟨i, hi⟩ := fun i hi => by
    have he : netE1 n + i < netE2 n := by change 2 * n + i < 4 * n; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B1 h t0 w (Nat.le_add_right _ _) he]
    apply congrArg w; apply Fin.ext; dsimp only; exact Nat.add_sub_cancel_left _ _
  have hB2 : ∀ leaf < 2 * treeM n, wireAt n x (netE2 n + leaf) = padLeaves n w leaf := fun leaf hl => by
    have he : netE2 n + leaf < netE3 n := by
      have : netE2 n = 4 * n := rfl; have : netE3 n = 4 * n + 2 * treeM n := rfl; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B2 h t0 w (Nat.le_add_right _ _) he,
        Nat.add_sub_cancel_left]
  have hB11 : ∀ tk < 2 * n, wireAt n x (netE11 n + tk) = mulWiresZ n h w tk := fun tk htk => by
    have he : netE11 n + tk < netE12 n := by have : netE12 n = netE11 n + 2 * n := rfl; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B11 h t0 w (Nat.le_add_right _ _) he,
        Nat.add_sub_cancel_left]
  have hB12 : ∀ locE < treeEdgeOff r (r + 1),
      wireAt n x (netE12 n + locE) = treeWireVal n w locE := fun locE hlocE => by
    have he : netE12 n + locE < netE13 n := by
      have : netE13 n = netE12 n + treeEdgeOff r (r + 1) := rfl; omega
    rw [wireAt_extWire h t0 w (by omega), rawExtWire_of_B12 h t0 w (Nat.le_add_right _ _) he,
        Nat.add_sub_cancel_left]
  have hB13 : ∀ k < W + 1, wireAt n x (netE13 n + k) = borrowWireVal mode n t0 w k := fun k hk => by
    have he : netE13 n + k < netEdgeCount n := by
      have : netEdgeCount n = netE13 n + (W + 1) := rfl; omega
    rw [wireAt_extWire h t0 w he, rawExtWire_of_B13 h t0 w (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
  by_cases hv13 : v.val < netV13 n
  · rw [eval_V12 mode n h s t0 t1 pre v x hv12 hv13]
    set i := v.val - netV12 n
    have hi : i < n := by have : netV13 n = netV12 n + n := rfl; omega
    have hdite : (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false) = zmod2ToBool (s ⟨i, hi⟩) :=
      dite_pos hi
    rw [hdite, hB1 i (by omega), hB11 i (by omega),
        show netE11 n + i + n = netE11 n + (i + n) by omega,
        hB11 (i + n) (by omega)]
    have he1_fn : (fun idx => if hlt : idx < n then zmod2ToBool ((decodeIfaceVec n w).2 ⟨idx, hlt⟩) else false) =
        e1Bit n w := by
      funext idx; unfold e1Bit decodeIfaceVec; dsimp only; split_ifs with hlt
      · exact zmod2ToBool_boolToZMod2 _
      · rfl
    have hcyc : twoLayerCycMul n h (decodeIfaceVec n w).2 ⟨i, hi⟩ =
        boolToZMod2 (bne (mulWiresZ n h w i) (mulWiresZ n h w (i + n))) := by
      unfold twoLayerCycMul mulWiresZ hBit; dsimp only; rw [he1_fn]
    have h_lhs : boolToZMod2 (bne (bne (w ⟨i, by omega⟩) (mulWiresZ n h w i)) (mulWiresZ n h w (i + n))) =
        boolToZMod2 (w ⟨i, by omega⟩) + boolToZMod2 (bne (mulWiresZ n h w i) (mulWiresZ n h w (i + n))) := by
      rw [boolToZMod2_bne, boolToZMod2_bne, add_assoc, ← boolToZMod2_bne]
    have hsyn2 : boolToZMod2 (bne (bne (w ⟨i, by omega⟩) (mulWiresZ n h w i)) (mulWiresZ n h w (i + n))) =
        s ⟨i, hi⟩ := by
      rw [h_lhs]
      have hsyn_orig := hval.2.1 ⟨i, hi⟩
      rwa [hcyc] at hsyn_orig
    have hz := congrArg zmod2ToBool hsyn2
    rwa [zmod2ToBool_boolToZMod2] at hz
  by_cases hv14 : v.val < netV14 n
  · set k := v.val - netV13 n
    have hk : k < treeM n - n := by have : netV14 n = netV13 n + (treeM n - n) := rfl; omega
    have hexp : expectedInc n v.val = [netE2 n + (n + k)] := by
      unfold expectedInc; rw [(inOut_of_V13 (by omega) hv14).1, (inOut_of_V13 (by omega) hv14).2]
      apply congrArg (· :: []); dsimp only [k]; omega
    rw [eval_pin_vertex mode n h s t0 t1 pre v x (netE2 n + (n + k)) (some false)
      (rawPred_of_V13 _ _ _ _ _ _ _ (by omega) hv14) hexp,
      hB2 (n + k) (by omega)]
    unfold padLeaves
    have hn1 : ¬(n + k < n) := by omega
    have hy : n + k < treeM n := by omega
    simp [hn1, hy]
  by_cases hv15 : v.val < netV15 n
  · set k := v.val - netV14 n
    have hk : k < treeM n - n := by have : netV15 n = netV14 n + (treeM n - n) := rfl; omega
    have hexp : expectedInc n v.val = [netE2 n + (treeM n + n + k)] := by
      unfold expectedInc; rw [(inOut_of_V14 (by omega) hv15).1, (inOut_of_V14 (by omega) hv15).2]
      apply congrArg (· :: []); dsimp only [k]; omega
    rw [eval_pin_vertex mode n h s t0 t1 pre v x (netE2 n + (treeM n + n + k)) (some false)
      (rawPred_of_V14 _ _ _ _ _ _ _ (by omega) hv15) hexp,
      hB2 (treeM n + n + k) (by omega)]
    unfold padLeaves
    have hn1 : ¬(treeM n + n + k < n) := by omega
    have hn2 : ¬(treeM n + n + k < treeM n) := by omega
    have hn3 : ¬(treeM n + n + k < treeM n + n) := by omega
    simp [hn1, hn2, hn3]
  by_cases hv16 : v.val < netV16 n
  · have hV16 : netV16 n = netV15 n + treeVertOff r (r + 1) := rfl
    set locV := v.val - netV15 n
    have hlocV : locV < treeVertOff r (r + 1) := by omega
    obtain ⟨hj1, hjr, hnode, hu_lt, _⟩ := decodeTreeVert_spec hlocV
    set tv := decodeTreeVert r locV
    set j := tv.1; set node := tv.2.1; set u := tv.2.2
    have htv : decodeTreeVert (treeLog n + 1) (v.val - netV15 n) = (j, node, u) :=
      Prod.ext rfl (Prod.ext rfl rfl)
    by_cases hu0 : u = 0
    · have hloc0 := encodeTreeEdge_lt hj1 hjr hnode (w := 0) (by omega)
      have hexp : expectedInc n v.val = [netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 0)] := by
        unfold expectedInc
        rw [inEdges_of_V15 (by omega) hv16 htv, outEdges_of_V15 (by omega) hv16 htv]
        dsimp only; simp only [hu0, ↓reduceIte, List.nil_append, List.cons.injEq, and_true]
        dsimp [r]; omega
      have hpred : rawPred mode n h s t0 t1 pre v.val = pinBitCircuit (some false) := by
        rw [rawPred_of_V15 _ _ _ _ _ _ _ (by omega) hv16 htv]; simp [hu0]
      rw [eval_pin_vertex mode n h s t0 t1 pre v x _ (some false) hpred hexp,
          hB12 _ hloc0]
      simpa [rippleCarry] using treeWireVal_even n w hj1 hjr hnode (b := 0) (by omega)
    · refine (eval_V15_fa mode n h s t0 t1 pre v x (by omega) hv16 htv hu0).mpr ?_
      set b := u - 1
      have hb_lt : b < j := by omega
      set A := treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node)
      set B := treeLevelBits (2 * treeM n) (padLeaves n w) (j - 1) (2 * node + 1)
      have hAB_val :
          wireAt n x (if j = 1 then netE2 n + 2 * node
                      else netE12 n + treeEdgeOff (treeLog n + 1) (j - 1) + (2 * node) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b) = A b ∧
          wireAt n x (if j = 1 then netE2 n + 2 * node + 1
                      else netE12 n + treeEdgeOff (treeLog n + 1) (j - 1) + (2 * node + 1) * (2 * (j - 1) + 1) + sumWireLoc (j - 1) b) = B b := by
        by_cases hj_eq1 : j = 1
        · have hb0 : b = 0 := by omega
          have hnode_M : node < treeM n := by
            have hr1 : r - 1 = treeLog n := rfl
            simpa [hj_eq1, hr1, treeM] using hnode
          simp only [hj_eq1, ↓reduceIte, hb0]
          have h2n0 : 2 * node < 2 * treeM n := by omega
          have h2n1 : 2 * node + 1 < 2 * treeM n := by omega
          have h1_eq : netE2 n + 2 * node + 1 = netE2 n + (2 * node + 1) := by omega
          rw [hB2 (2 * node) h2n0, h1_eq, hB2 (2 * node + 1) h2n1]
          dsimp [A, B]; simp [hj_eq1, treeLevelBits, h2n0, h2n1]
        · simp only [hj_eq1, ↓reduceIte]
          set j' := j - 1
          have hj'1 : 1 ≤ j' := by omega
          have hj'r : j' ≤ r := by omega
          have hb_le : b ≤ j' := by omega
          have hexp : r - j' = (r - j) + 1 := by omega
          have hc0 : 2 * node < 2 ^ (r - j') := by rw [hexp, pow_succ']; omega
          have hc1 : 2 * node + 1 < 2 ^ (r - j') := by rw [hexp, pow_succ']; omega
          have hsw : sumWireLoc j' b < 2 * j' + 1 := sumWireLoc_lt hb_le
          have hlocL := encodeTreeEdge_lt hj'1 hj'r hc0 hsw
          have hlocR := encodeTreeEdge_lt hj'1 hj'r hc1 hsw
          have heL : netE12 n + treeEdgeOff (treeLog n + 1) j' + (2 * node) * (2 * j' + 1) + sumWireLoc j' b =
              netE12 n + (treeEdgeOff r j' + (2 * node) * (2 * j' + 1) + sumWireLoc j' b) := by dsimp [r]; omega
          have heR : netE12 n + treeEdgeOff (treeLog n + 1) j' + (2 * node + 1) * (2 * j' + 1) + sumWireLoc j' b =
              netE12 n + (treeEdgeOff r j' + (2 * node + 1) * (2 * j' + 1) + sumWireLoc j' b) := by dsimp [r]; omega
          rw [heL, hB12 _ hlocL, treeWireVal_sumWireLoc n w hj'1 hj'r hc0 hb_le,
              heR, hB12 _ hlocR, treeWireVal_sumWireLoc n w hj'1 hj'r hc1 hb_le]
          exact ⟨rfl, rfl⟩
      have hloc_cin := encodeTreeEdge_lt hj1 hjr hnode (w := 2 * b) (by omega)
      have hloc_sum := encodeTreeEdge_lt hj1 hjr hnode (w := 2 * b + 1) (by omega)
      have hloc_cout := encodeTreeEdge_lt hj1 hjr hnode (w := 2 * (b + 1)) (by omega)
      have he_cin : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b =
          netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * b) := by dsimp [r]; omega
      have he_sum : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b + 1 =
          netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + (2 * b + 1)) := by dsimp [r]; omega
      have he_cout : netE12 n + treeEdgeOff (treeLog n + 1) j + node * (2 * j + 1) + 2 * b + 2 =
          netE12 n + (treeEdgeOff r j + node * (2 * j + 1) + 2 * (b + 1)) := by dsimp [r]; omega
      rw [hAB_val.1, hAB_val.2, he_sum, he_cout, he_cin,
          hB12 _ hloc_cin, hB12 _ hloc_sum, hB12 _ hloc_cout,
          treeWireVal_even n w hj1 hjr hnode (by omega),
          treeWireVal_odd n w hj1 hjr hnode hb_lt,
          treeWireVal_even n w hj1 hjr hnode (by omega)]
      refine ⟨rfl, rfl, ?_⟩
      rintro ⟨hm2, hj_eq_r⟩
      have hwt := hval.2.2
      rw [hm2] at hwt
      simp only [ModeWeightCond, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hwt
      rw [← padLeaves_wt0 n w, ← padLeaves_wt1 n w] at hwt
      change bitsVal r _ = t0 ∧ bitsVal r _ = t1 at hwt
      rw [bitsVal_eq_iff_testBit, bitsVal_eq_iff_testBit] at hwt
      have hnode0 : node = 0 := by rw [hj_eq_r, Nat.sub_self, pow_zero] at hnode; omega
      have hr_sub : j - 1 = treeLog n := by rw [hj_eq_r]; rfl
      have hb_r : b < r := by omega
      dsimp [A, B]
      rw [hr_sub, hnode0]
      exact ⟨hwt.1.1, hwt.2.1, hwt.1.2 b hb_r, hwt.2.2 b hb_r⟩
  by_cases hv17 : v.val < netV17 n
  · have hexp : expectedInc n v.val = [netE13 n] := by
      unfold expectedInc; rw [(inOut_of_V16 (by omega) hv17).1, (inOut_of_V16 (by omega) hv17).2, List.nil_append]
    rw [eval_pin_vertex mode n h s t0 t1 pre v x (netE13 n) (some false)
      (rawPred_of_V16 _ _ _ _ _ _ _ (by omega) hv17) hexp]
    have h0 := hB13 0 (by omega)
    rw [Nat.add_zero] at h0; rw [h0]
    unfold borrowWireVal; split_ifs <;> rfl
  by_cases hv18 : v.val < netV18 n
  · refine (eval_V17 mode n h s t0 t1 pre v x (by omega) hv18).mpr ?_
    set b := v.val - netV17 n
    have hb_lt : b < W := by have : netV18 n = netV17 n + W := rfl; omega
    have hb_le : b ≤ r := by dsimp [r, W] at hb_lt ⊢; omega
    have hsw : sumWireLoc r b < 2 * r + 1 := sumWireLoc_lt hb_le
    have hlocE := encodeTreeEdge_lt (r := r) (j := r) (node := 0) (by dsimp [r]; omega) le_rfl (by simp) hsw
    have heSum_eq : netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 1) + sumWireLoc (treeLog n + 1) b =
        netE12 n + (treeEdgeOff r r + 0 * (2 * r + 1) + sumWireLoc r b) := by dsimp [r]; omega
    have he13_next : netE13 n + b + 1 = netE13 n + (b + 1) := by omega
    rw [heSum_eq, hB12 _ hlocE, treeWireVal_sumWireLoc n w (by omega) le_rfl (by simp) hb_le,
        hB13 b (by omega), he13_next, hB13 (b + 1) (by omega)]
    by_cases hm0 : mode = 0
    · subst hm0
      simp only [↓reduceIte, borrowWireVal, show ¬(0 = 1) by decide, and_true]
      have hwt := hval.2.2
      simp only [ModeWeightCond, ↓reduceIte] at hwt
      rw [← padLeaves_wt_sum n w] at hwt
      change bitsVal W _ = t0 at hwt
      rw [bitsVal_eq_iff_testBit] at hwt
      exact ⟨hwt.1, hwt.2 b hb_lt⟩
    · simp only [hm0, ↓reduceIte]
      by_cases hm1 : mode = 1
      · subst hm1
        simp [borrowWireVal, leBorrow]
      · simp [borrowWireVal, hm1]
  · rw [eval_V18 mode n h s t0 t1 pre v x (by omega)]
    by_cases hc : mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2))
    · simp [hc]
    · rw [ite_neg hc, hB13 W (by omega)]
      by_cases hm1 : mode = 1
      · subst hm1
        have ht_lt : t0 < 2 ^ W := by dsimp [W]; omega
        unfold borrowWireVal; simp only [↓reduceIte]
        have hwt := hval.2.2
        simp only [ModeWeightCond, show ¬(1 = 0) by decide, ↓reduceIte] at hwt
        rw [← padLeaves_wt_sum n w] at hwt
        change bitsVal W _ ≤ t0 at hwt
        rw [bitsVal_le_iff_leBorrow W _ t0, ite_pos ht_lt] at hwt
        exact hwt
      · unfold borrowWireVal; simp [hm1]

/-- Exact characterization of satisfying assignments of `buildQCSDNet` for `mode ≤ 2`. -/
theorem buildQCSDNet_sat_iff {mode : ℕ} (hmode : mode ≤ 2) (n : ℕ)
    (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (x : Fin (netEdgeCount n) → Bool) :
    (∀ v : Fin (netVertCount n), vertexSat (buildQCSDNet mode n h s t0 t1 pre) v x = true) ↔
      ∃ w : Fin (2 * n) → Bool,
        ValidModeIface mode n h s t0 t1 pre w ∧ x = extWire mode n h t0 w := by
  constructor
  · intro hsat
    set w : Fin (2 * n) → Bool :=
      fun i => x ⟨i.val, lt_of_lt_of_le i.isLt (netE1_le_netEdgeCount n)⟩
    obtain ⟨hpre, hE0_11, hsyn⟩ := sat_imp_mul_and_syn mode n h s t0 t1 pre x hsat
    have hE2 : ∀ leaf < 2 * treeM n, wireAt n x (netE2 n + leaf) = padLeaves n w leaf := by
      intro leaf hl
      rcases netE_chain n with ⟨_, _, _, h34, h45, h56, h67, h78, h89, h910, h1011, h1112, _, _⟩
      have he3 : netE2 n + leaf < netE3 n := by
        have : netE2 n = 4 * n := rfl; have : netE3 n = 4 * n + 2 * treeM n := rfl; omega
      rw [hE0_11 (netE2 n + leaf) (by omega),
          rawExtWire_of_B2 h t0 w (Nat.le_add_right _ _) he3, Nat.add_sub_cancel_left]
    obtain ⟨hE12_13, hwt⟩ := sat_imp_tree_and_cmp hmode n h s t0 t1 pre x hsat w hE2
    refine ⟨w, ⟨hpre, hsyn, hwt⟩, ?_⟩
    funext e
    rw [← wireAt_lt x e.isLt]
    by_cases he12 : e.val < netE12 n
    · exact hE0_11 e.val he12
    · exact hE12_13 e.val (by omega) e.isLt
  · rintro ⟨w, hval, rfl⟩ v
    by_cases hv12 : v.val < netV12 n
    · exact extWire_sat_0_11 mode n h s t0 t1 pre w hval.1 v hv12
    · exact extWire_sat_12_18 hmode n h s t0 t1 pre w hval v (by omega)

theorem buildQCSDNet_contraction {mode : ℕ} (hmode : mode ≤ 2) (n : ℕ)
    (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_contraction2 (buildQCSDNet mode n h s t0 t1 pre) =
      haveI := Classical.decPred (ValidModeIface mode n h s t0 t1 pre)
      (Finset.univ.filter (ValidModeIface mode n h s t0 t1 pre)).card := by
  exact @contraction2_eq_card_validIface
    (buildQCSDNet mode n h s t0 t1 pre)
    (2 * n)
    (netE1_le_netEdgeCount n)
    (extWire mode n h t0)
    (ValidModeIface mode n h s t0 t1 pre)
    (Classical.decPred (ValidModeIface mode n h s t0 t1 pre))
    (extWire_iface mode n h t0)
    (buildQCSDNet_sat_iff hmode n h s t0 t1 pre)

/-! ### Master Contraction & Witness Decoding Theorems (`N_exact`, `N_le`, `N_sep`) -/

/-- Exact solution-count preservation for `N_exact inp pre` (§4.1–§4.2, §5.1). -/
theorem N_exact_contraction (inp : QCSD_Instance) (pre : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (N_exact inp pre) =
      ((QCSD_solutions inp).filter
        (fun q => (QCSD_iface inp.n q.1 q.2).take pre.length = pre)).card := by
  unfold N_exact
  rw [buildQCSDNet_contraction (by decide)]
  classical
  apply Finset.card_bij (fun (w : Fin (2 * inp.n) → Bool) _ => decodeIfaceVec inp.n w)
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hw_pre, hw_syn, hw_wt⟩ := hw.2
    simp only [ModeWeightCond, ↓reduceIte] at hw_wt
    refine ⟨?_, ?_⟩
    · unfold QCSD_solutions
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hw_wt⟩
      intro k
      have hk := hw_syn k
      rwa [hconv inp.h (decodeIfaceVec inp.n w).2 k] at hk
    · rw [iface_take_eq_iff _ hpre, ifaceVec_decodeIfaceVec]
      exact hw_pre
  · intro w1 _ w2 _ heq
    rw [← ifaceVec_decodeIfaceVec inp.n w1, ← ifaceVec_decodeIfaceVec inp.n w2, heq]
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hq_sol, hq_pre⟩ := hq
    unfold QCSD_solutions at hq_sol
    rw [Finset.mem_filter] at hq_sol
    refine ⟨ifaceVec inp.n q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      decodeIfaceVec_ifaceVec inp.n q⟩
    unfold ValidModeIface
    rw [decodeIfaceVec_ifaceVec inp.n q]
    refine ⟨(iface_take_eq_iff q hpre).mp hq_pre, ?_, ?_⟩
    · intro k
      rw [hconv inp.h q.2 k]
      exact hq_sol.2.1 k
    · simp [ModeWeightCond, hq_sol.2.2]

/-- Exact solution-count preservation for `N_le inp pre` (§4.1–§4.2, §5.1). -/
theorem N_le_contraction (inp : QCSD_Instance) (pre : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (N_le inp pre) =
      ((QCSD_solutionsLe inp).filter
        (fun q => (QCSD_iface inp.n q.1 q.2).take pre.length = pre)).card := by
  unfold N_le
  rw [buildQCSDNet_contraction (by decide)]
  classical
  apply Finset.card_bij (fun (w : Fin (2 * inp.n) → Bool) _ => decodeIfaceVec inp.n w)
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hw_pre, hw_syn, hw_wt⟩ := hw.2
    simp only [ModeWeightCond, show ¬(1 = 0) by decide, ↓reduceIte] at hw_wt
    refine ⟨?_, ?_⟩
    · unfold QCSD_solutionsLe
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hw_wt⟩
      intro k
      have hk := hw_syn k
      rwa [hconv inp.h (decodeIfaceVec inp.n w).2 k] at hk
    · rw [iface_take_eq_iff _ hpre, ifaceVec_decodeIfaceVec]
      exact hw_pre
  · intro w1 _ w2 _ heq
    rw [← ifaceVec_decodeIfaceVec inp.n w1, ← ifaceVec_decodeIfaceVec inp.n w2, heq]
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hq_sol, hq_pre⟩ := hq
    unfold QCSD_solutionsLe at hq_sol
    rw [Finset.mem_filter] at hq_sol
    refine ⟨ifaceVec inp.n q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      decodeIfaceVec_ifaceVec inp.n q⟩
    unfold ValidModeIface
    rw [decodeIfaceVec_ifaceVec inp.n q]
    refine ⟨(iface_take_eq_iff q hpre).mp hq_pre, ?_, ?_⟩
    · intro k
      rw [hconv inp.h q.2 k]
      exact hq_sol.2.1 k
    · simp [ModeWeightCond, hq_sol.2.2]

/-- Exact solution-count preservation for `N_sep inp pre` (§4.1–§4.2, §5.1). -/
theorem N_sep_contraction (inp : QCSD_InstanceSep) (pre : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (N_sep inp pre) =
      ((QCSD_solutionsSep inp).filter
        (fun q => (QCSD_iface inp.n q.1 q.2).take pre.length = pre)).card := by
  unfold N_sep
  rw [buildQCSDNet_contraction (by decide)]
  classical
  apply Finset.card_bij (fun (w : Fin (2 * inp.n) → Bool) _ => decodeIfaceVec inp.n w)
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hw_pre, hw_syn, hw_wt⟩ := hw.2
    simp only [ModeWeightCond, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hw_wt
    refine ⟨?_, ?_⟩
    · unfold QCSD_solutionsSep
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hw_wt⟩
      intro k
      have hk := hw_syn k
      rwa [hconv inp.h (decodeIfaceVec inp.n w).2 k] at hk
    · rw [iface_take_eq_iff _ hpre, ifaceVec_decodeIfaceVec]
      exact hw_pre
  · intro w1 _ w2 _ heq
    rw [← ifaceVec_decodeIfaceVec inp.n w1, ← ifaceVec_decodeIfaceVec inp.n w2, heq]
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hq_sol, hq_pre⟩ := hq
    unfold QCSD_solutionsSep at hq_sol
    rw [Finset.mem_filter] at hq_sol
    refine ⟨ifaceVec inp.n q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      decodeIfaceVec_ifaceVec inp.n q⟩
    unfold ValidModeIface
    rw [decodeIfaceVec_ifaceVec inp.n q]
    refine ⟨(iface_take_eq_iff q hpre).mp hq_pre, ?_, ?_⟩
    · intro k
      rw [hconv inp.h q.2 k]
      exact hq_sol.2.1 k
    · simp [ModeWeightCond, hq_sol.2.2]

/-- Empty-prefix (`pre = []`) exact count corollaries. -/
theorem N_exact_contraction_nil (inp : QCSD_Instance) (hconv : TwoLayerConvSpec inp.n) :
    QCSD_contraction2 (N_exact inp []) = QCSD_count inp := by
  rw [N_exact_contraction inp [] hconv (by simp)]
  simp [QCSD_count]

theorem N_le_contraction_nil (inp : QCSD_Instance) (hconv : TwoLayerConvSpec inp.n) :
    QCSD_contraction2 (N_le inp []) = QCSD_countLe inp := by
  rw [N_le_contraction inp [] hconv (by simp)]
  simp [QCSD_countLe]

theorem N_sep_contraction_nil (inp : QCSD_InstanceSep) (hconv : TwoLayerConvSpec inp.n) :
    QCSD_contraction2 (N_sep inp []) = QCSD_countSep inp := by
  rw [N_sep_contraction inp [] hconv (by simp)]
  simp [QCSD_countSep]

/-- Generic helper evaluating filtered solution cardinality at a full `2 * n`-bit prefix `w`. -/
lemma filter_full_prefix_card {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (P : (Fin n → ZMod 2) → (Fin n → ZMod 2) → Prop)
    (hsols : ∀ q, q ∈ sols ↔ P q.1 q.2)
    (w : List Bool) (hw : w.length = 2 * n) :
    (sols.filter (fun q => (QCSD_iface n q.1 q.2).take w.length = w)).card =
      (haveI := Classical.propDecidable
       if ∃ e₀ e₁, QCSD_decodeSolPair n w = some (e₀, e₁) ∧ P e₀ e₁ then 1 else 0) := by
  have hdec_some : ∃ p0, QCSD_decodeSolPair n w = some p0 := by
    unfold QCSD_decodeSolPair
    rw [ite_pos hw]
    exact ⟨_, rfl⟩
  obtain ⟨⟨e0, e1⟩, hdec⟩ := hdec_some
  have hq_iff : ∀ q : (Fin n → ZMod 2) × (Fin n → ZMod 2),
      q ∈ sols.filter (fun q => (QCSD_iface n q.1 q.2).take w.length = w) ↔
        (e0, e1) ∈ sols ∧ q = (e0, e1) := by
    intro q
    rw [Finset.mem_filter]
    have htk : (QCSD_iface n q.1 q.2).take w.length = QCSD_iface n q.1 q.2 := by
      rw [hw, ← iface_length n q.1 q.2, List.take_length]
    rw [htk, iface_eq_iff_decodeSolPair q.1 q.2, hdec]
    have hq_eq : some (e0, e1) = some (q.1, q.2) ↔ q = (e0, e1) := by
      rcases q with ⟨q0, q1⟩
      simp [eq_comm]
    rw [hq_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2.symm ▸ h1, h2⟩⟩
  have hex_iff : (∃ a b, QCSD_decodeSolPair n w = some (a, b) ∧ P a b) ↔ (e0, e1) ∈ sols := by
    rw [hsols (e0, e1)]
    constructor
    · rintro ⟨a, b, hab, hp⟩
      rw [hdec] at hab
      injection hab with hp_eq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp_eq
      exact hp
    · intro hp
      exact ⟨e0, e1, hdec, hp⟩
  by_cases hex : ∃ a b, QCSD_decodeSolPair n w = some (a, b) ∧ P a b
  · have hmem : (e0, e1) ∈ sols := hex_iff.mp hex
    rw [@ite_pos _ _ (Classical.propDecidable _) hex]
    refine Finset.card_eq_one.mpr ⟨(e0, e1), ?_⟩
    ext q
    rw [hq_iff q, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  · have hmem : (e0, e1) ∉ sols := fun hm => hex (hex_iff.mpr hm)
    rw [@ite_neg _ _ (Classical.propDecidable _) hex]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    exact hmem ((hq_iff q).mp hq).1

/-- Full-prefix (`w.length = 2 * inp.n`) witness decoding equivalence for `N_exact` (§5.1). -/
theorem N_exact_full_prefix_eq (inp : QCSD_Instance) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    QCSD_contraction2 (N_exact inp w) =
      (haveI := Classical.propDecidable
       if ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSol inp e₀ e₁ then 1 else 0) := by
  rw [N_exact_contraction inp w hconv (le_of_eq hw)]
  refine filter_full_prefix_card (QCSD_solutions inp) (QCSD_IsSol inp) (fun q => ?_) w hw
  classical
  unfold QCSD_solutions
  simp

theorem N_exact_full_prefix_iff (inp : QCSD_Instance) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    (1 ≤ QCSD_contraction2 (N_exact inp w) ↔
      ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSol inp e₀ e₁) ∧
    QCSD_contraction2 (N_exact inp w) ≤ 1 := by
  rw [N_exact_full_prefix_eq inp w hconv hw]
  by_cases h : ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSol inp e₀ e₁
  · rw [@ite_pos _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun _ => h, fun _ => le_rfl⟩, le_rfl⟩
  · rw [@ite_neg _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun h1 => absurd h1 (by decide), fun hh => absurd hh h⟩, by decide⟩

/-- Full-prefix (`w.length = 2 * inp.n`) witness decoding equivalence for `N_le` (§5.1). -/
theorem N_le_full_prefix_eq (inp : QCSD_Instance) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    QCSD_contraction2 (N_le inp w) =
      (haveI := Classical.propDecidable
       if ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolLe inp e₀ e₁ then 1 else 0) := by
  rw [N_le_contraction inp w hconv (le_of_eq hw)]
  refine filter_full_prefix_card (QCSD_solutionsLe inp) (QCSD_IsSolLe inp) (fun q => ?_) w hw
  classical
  unfold QCSD_solutionsLe
  simp

theorem N_le_full_prefix_iff (inp : QCSD_Instance) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    (1 ≤ QCSD_contraction2 (N_le inp w) ↔
      ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolLe inp e₀ e₁) ∧
    QCSD_contraction2 (N_le inp w) ≤ 1 := by
  rw [N_le_full_prefix_eq inp w hconv hw]
  by_cases h : ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolLe inp e₀ e₁
  · rw [@ite_pos _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun _ => h, fun _ => le_rfl⟩, le_rfl⟩
  · rw [@ite_neg _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun h1 => absurd h1 (by decide), fun hh => absurd hh h⟩, by decide⟩

/-- Full-prefix (`w.length = 2 * inp.n`) witness decoding equivalence for `N_sep` (§5.1). -/
theorem N_sep_full_prefix_eq (inp : QCSD_InstanceSep) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    QCSD_contraction2 (N_sep inp w) =
      (haveI := Classical.propDecidable
       if ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolSep inp e₀ e₁ then 1 else 0) := by
  rw [N_sep_contraction inp w hconv (le_of_eq hw)]
  refine filter_full_prefix_card (QCSD_solutionsSep inp) (QCSD_IsSolSep inp) (fun q => ?_) w hw
  classical
  unfold QCSD_solutionsSep
  simp

theorem N_sep_full_prefix_iff (inp : QCSD_InstanceSep) (w : List Bool)
    (hconv : TwoLayerConvSpec inp.n) (hw : w.length = 2 * inp.n) :
    (1 ≤ QCSD_contraction2 (N_sep inp w) ↔
      ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolSep inp e₀ e₁) ∧
    QCSD_contraction2 (N_sep inp w) ≤ 1 := by
  rw [N_sep_full_prefix_eq inp w hconv hw]
  by_cases h : ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolSep inp e₀ e₁
  · rw [@ite_pos _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun _ => h, fun _ => le_rfl⟩, le_rfl⟩
  · rw [@ite_neg _ _ (Classical.propDecidable _) h]
    exact ⟨⟨fun h1 => absurd h1 (by decide), fun hh => absurd hh h⟩, by decide⟩

end Branch3






