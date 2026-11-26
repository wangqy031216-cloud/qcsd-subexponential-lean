import Branch5_PadAndSep

namespace Branch7EncodeSpec

open QCSD.Defs
open Branch5PadAndSep

/-!
## Section 1: Master Network Bit-Stream Formulas (`QCSD_encodeNet2` & `padNet`)
-/

lemma map_val_finRange :
    ∀ (m : ℕ), (List.finRange m).map Fin.val = List.range m := by
  intro m
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- Converts any `(List.finRange m).flatMap f` into an index-only `(List.range m).flatMap g`. -/
theorem finRange_flatMap_eq_range_flatMap {α : Type*} (m : ℕ)
    (f : Fin m → List α) (g : ℕ → List α)
    (hfg : ∀ i : Fin m, f i = g i.val) :
    (List.finRange m).flatMap f = (List.range m).flatMap g := by
  rw [← map_val_finRange m, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => hfg i)

/-- Unpadded network stream formula replacing `Fin` iterators by pure `List.range` `ℕ` loops. -/
theorem encodeNet2_stream_eq (N : QCSD_BoolTensorNetwork2)
    (rawEnds : ℕ → ℕ × ℕ) (rawPred : ℕ → QCSD_BoolCircuit)
    (hEnds : ∀ e : Fin N.k, ((N.ends e).1.val, (N.ends e).2.val) = rawEnds e.val)
    (hPred : ∀ v : Fin N.m, N.pred v = rawPred v.val) :
    QCSD_encodeNet2 N =
      List.replicate N.m true ++ [false] ++
      QCSD_natToUnary N.k ++
      (List.range N.k).flatMap (fun e =>
        QCSD_natToUnary (rawEnds e).1 ++ QCSD_natToUnary (rawEnds e).2) ++
      (List.range N.m).flatMap (fun v => QCSD_encodeCircuit (rawPred v)) := by
  unfold QCSD_encodeNet2
  have hunary_m : QCSD_natToUnary N.m = List.replicate N.m true ++ [false] := rfl
  have hends_eq :
      (List.finRange N.k).flatMap (fun e =>
        QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val) =
      (List.range N.k).flatMap (fun e =>
        QCSD_natToUnary (rawEnds e).1 ++ QCSD_natToUnary (rawEnds e).2) := by
    apply finRange_flatMap_eq_range_flatMap
    intro e
    have he := hEnds e
    rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
  have hpreds_eq :
      (List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v)) =
      (List.range N.m).flatMap (fun v => QCSD_encodeCircuit (rawPred v)) := by
    apply finRange_flatMap_eq_range_flatMap
    intro v
    rw [hPred v]
  rw [hunary_m, hends_eq, hpreds_eq]

/-- **Master Network Stream Formula**: exact `List.range` bit-stream representation of
`QCSD_encodeNet2 (padNet padV N)` in terms of `rawEnds` and `rawPred`. -/
theorem encodeNet2_padNet_stream_eq (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (rawEnds : ℕ → ℕ × ℕ) (rawPred : ℕ → QCSD_BoolCircuit)
    (hEnds : ∀ e : Fin N.k, ((N.ends e).1.val, (N.ends e).2.val) = rawEnds e.val)
    (hPred : ∀ v : Fin N.m, N.pred v = rawPred v.val) :
    QCSD_encodeNet2 (padNet padV N) =
      List.replicate (N.m + padV) true ++ [false] ++
      QCSD_natToUnary N.k ++
      (List.range N.k).flatMap (fun e =>
        QCSD_natToUnary (rawEnds e).1 ++ QCSD_natToUnary (rawEnds e).2) ++
      (List.range N.m).flatMap (fun v => QCSD_encodeCircuit (rawPred v)) ++
      (List.range padV).flatMap (fun _ => [false, true, false, false, false, true]) := by
  rw [encodeNet2_padNet_decomp, encodeNet2_stream_eq N rawEnds rawPred hEnds hPred]
  have hpad_tail :
      (List.finRange padV).flatMap (fun _ => QCSD_encodeCircuit constTrueZeroIn) =
      (List.range padV).flatMap (fun _ => [false, true, false, false, false, true]) := by
    apply finRange_flatMap_eq_range_flatMap
    intro _
    exact constTrueZeroIn_encode
  have hrep :
      List.replicate padV true ++ List.replicate N.m true =
      List.replicate (N.m + padV) true := by
    rw [Nat.add_comm N.m padV, List.replicate_add]
  rw [hpad_tail]
  simp only [← List.append_assoc]
  rw [hrep]

/-- **Workspace-Split Master Network Stream Formula**: for any workspace overwrite width
`W ≤ N.m + padV` (such as `W = 3 * M_blk` in `blkSweepTrue`), splits `QCSD_encodeNet2 (padNet padV N)`
into `List.replicate W true ++ emittedTail` byte-for-byte. -/
theorem encodeNet2_padNet_stream_split (padV W : ℕ) (N : QCSD_BoolTensorNetwork2)
    (rawEnds : ℕ → ℕ × ℕ) (rawPred : ℕ → QCSD_BoolCircuit)
    (hW : W ≤ N.m + padV)
    (hEnds : ∀ e : Fin N.k, ((N.ends e).1.val, (N.ends e).2.val) = rawEnds e.val)
    (hPred : ∀ v : Fin N.m, N.pred v = rawPred v.val) :
    QCSD_encodeNet2 (padNet padV N) =
      List.replicate W true ++
      (List.replicate (N.m + padV - W) true ++ [false] ++
       QCSD_natToUnary N.k ++
       (List.range N.k).flatMap (fun e =>
         QCSD_natToUnary (rawEnds e).1 ++ QCSD_natToUnary (rawEnds e).2) ++
       (List.range N.m).flatMap (fun v => QCSD_encodeCircuit (rawPred v)) ++
       (List.range padV).flatMap (fun _ => [false, true, false, false, false, true])) := by
  rw [encodeNet2_padNet_stream_eq padV N rawEnds rawPred hEnds hPred]
  have hadd : W + (N.m + padV - W) = N.m + padV := by omega
  have hsplit :
      List.replicate (N.m + padV) true =
        List.replicate W true ++ List.replicate (N.m + padV - W) true := by
    conv_lhs => rw [← hadd]
    exact List.replicate_add W (N.m + padV - W) true
  rw [hsplit]
  simp only [List.append_assoc]

/-- Direct `W = padV` specialization (`N.m + W - W = N.m`). -/
theorem encodeNet2_padNet_stream_split_exact (W : ℕ) (N : QCSD_BoolTensorNetwork2)
    (rawEnds : ℕ → ℕ × ℕ) (rawPred : ℕ → QCSD_BoolCircuit)
    (hEnds : ∀ e : Fin N.k, ((N.ends e).1.val, (N.ends e).2.val) = rawEnds e.val)
    (hPred : ∀ v : Fin N.m, N.pred v = rawPred v.val) :
    QCSD_encodeNet2 (padNet W N) =
      List.replicate W true ++
      (List.replicate N.m true ++ [false] ++
       QCSD_natToUnary N.k ++
       (List.range N.k).flatMap (fun e =>
         QCSD_natToUnary (rawEnds e).1 ++ QCSD_natToUnary (rawEnds e).2) ++
       (List.range N.m).flatMap (fun v => QCSD_encodeCircuit (rawPred v)) ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) := by
  have h := encodeNet2_padNet_stream_split W W N rawEnds rawPred (Nat.le_add_left W N.m) hEnds hPred
  simpa [Nat.add_sub_cancel] using h

/-!
## Section 2: Circuit Combinators (Definitionally Equal to `Branch3`) & Primitive Gate Encodings
-/

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

def emitXorListAux : List QCSD_Gate → ℕ → List ℕ → List QCSD_Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitXor gs acc w
    emitXorListAux r.1 r.2 ws

def emitXorList (gs : List QCSD_Gate) (ws : List ℕ) : List QCSD_Gate × ℕ :=
  let r0 := emitConst gs false
  emitXorListAux r0.1 r0.2 ws

def emitAllAux : List QCSD_Gate → ℕ → List ℕ → List QCSD_Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitConj gs acc w
    emitAllAux r.1 r.2 ws

def emitAll (gs : List QCSD_Gate) (ws : List ℕ) : List QCSD_Gate × ℕ :=
  let r0 := emitConst gs true
  emitAllAux r0.1 r0.2 ws

def initInputs (numIn : ℕ) : List QCSD_Gate :=
  (List.range numIn).map (fun i => ⟨QCSD_GateOp.input, i, 0⟩)

def constCircuit (numIn : ℕ) (b : Bool) : QCSD_BoolCircuit :=
  ⟨numIn, [⟨if b then QCSD_GateOp.tt else QCSD_GateOp.ff, 0, 0⟩]⟩

def pinBitCircuit : Option Bool → QCSD_BoolCircuit
  | none => constCircuit 1 true
  | some true => ⟨1, [⟨QCSD_GateOp.input, 0, 0⟩]⟩
  | some false => ⟨1, [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.neg, 0, 0⟩]⟩

def guardedBitCircuit (guard target : Bool) : QCSD_BoolCircuit :=
  if guard then pinBitCircuit (some target) else constCircuit 1 false

def synCheckCircuit (target : Bool) : QCSD_BoolCircuit :=
  let gs0 : List QCSD_Gate :=
    [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩]
  let r1 := emitXor gs0 0 1
  let r2 := emitXor r1.1 r1.2 2
  let r3 := emitConst r2.1 target
  let r4 := emitEq r3.1 r2.2 r3.2
  ⟨3, r4.1⟩

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

def borrowStepCircuit (tBit : Bool) : QCSD_BoolCircuit :=
  let gs0 : List QCSD_Gate :=
    [⟨QCSD_GateOp.input, 0, 0⟩, ⟨QCSD_GateOp.input, 1, 0⟩, ⟨QCSD_GateOp.input, 2, 0⟩]
  let rstep := if tBit then emitConj gs0 0 1 else emitDisj gs0 0 1
  let req := emitEq rstep.1 2 rstep.2
  ⟨3, req.1⟩

def sepCmpStepCircuit : QCSD_BoolCircuit :=
  ⟨3, [⟨QCSD_GateOp.input, 2, 0⟩, ⟨QCSD_GateOp.neg, 0, 0⟩]⟩

def emitParityChecks : List QCSD_Gate → List (ℕ × List ℕ) → List QCSD_Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, (outW, inWs) :: rest =>
    let rx := emitXorList gs inWs
    let req := emitEq rx.1 outW rx.2
    let rrest := emitParityChecks req.1 rest
    (rrest.1, req.2 :: rrest.2)

def linearMapCheckCircuit (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) : QCSD_BoolCircuit :=
  let totalIn := numIn + numOut
  let gs0 := initInputs totalIn
  let specs := (List.range numOut).map (fun j =>
    (numIn + j, (List.range numIn).filter (fun i => mat j i)))
  let rpc := emitParityChecks gs0 specs
  let rall := emitAll rpc.1 rpc.2
  ⟨totalIn, rall.1⟩

def emitPairConjs : List QCSD_Gate → List (ℕ × ℕ) → List QCSD_Gate
  | gs, [] => gs
  | gs, (a, b) :: rest =>
    let rc := emitConj gs a b
    emitPairConjs rc.1 rest

def bilinearPairs (n1 n2 : ℕ) : List (ℕ × ℕ) :=
  (List.range (n1 * n2)).map (fun k => (k / n2, n1 + k % n2))

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

/-! ### Closed-Form `QCSD_encodeGate` & Multi-Gate Block Bit Streams -/

@[simp] theorem encodeGate_input (i a2 : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.input, i, a2⟩ = [false, false, false] ++ QCSD_natToUnary i := rfl

@[simp] theorem encodeGate_tt (a1 a2 : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.tt, a1, a2⟩ = [false, false, true] := rfl

@[simp] theorem encodeGate_ff (a1 a2 : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.ff, a1, a2⟩ = [false, true, false] := rfl

@[simp] theorem encodeGate_neg (a a2 : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.neg, a, a2⟩ = [false, true, true] ++ QCSD_natToUnary a := rfl

@[simp] theorem encodeGate_conj (a b : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.conj, a, b⟩ =
      [true, false, false] ++ QCSD_natToUnary a ++ QCSD_natToUnary b := by
  simp [QCSD_encodeGate, QCSD_gateTag]

@[simp] theorem encodeGate_disj (a b : ℕ) :
    QCSD_encodeGate ⟨QCSD_GateOp.disj, a, b⟩ =
      [true, false, true] ++ QCSD_natToUnary a ++ QCSD_natToUnary b := by
  simp [QCSD_encodeGate, QCSD_gateTag]

theorem encodeGate_constBool (b : Bool) :
    QCSD_encodeGate ⟨if b then QCSD_GateOp.tt else QCSD_GateOp.ff, 0, 0⟩ =
      if b then [false, false, true] else [false, true, false] := by
  cases b <;> rfl

/-- The 5-gate XOR gadget emitted starting at wire offset `o = gs.length`. -/
def xorGatesAt (o a b : ℕ) : List QCSD_Gate :=
  [⟨QCSD_GateOp.neg, b, 0⟩,
   ⟨QCSD_GateOp.conj, a, o⟩,
   ⟨QCSD_GateOp.neg, a, 0⟩,
   ⟨QCSD_GateOp.conj, o + 2, b⟩,
   ⟨QCSD_GateOp.disj, o + 1, o + 3⟩]

/-- Exact bit-stream emitted by `xorGatesAt o a b`. -/
def encodeXorAt (o a b : ℕ) : List Bool :=
  [false, true, true] ++ QCSD_natToUnary b ++
  [true, false, false] ++ QCSD_natToUnary a ++ QCSD_natToUnary o ++
  [false, true, true] ++ QCSD_natToUnary a ++
  [true, false, false] ++ QCSD_natToUnary (o + 2) ++ QCSD_natToUnary b ++
  [true, false, true] ++ QCSD_natToUnary (o + 1) ++ QCSD_natToUnary (o + 3)

@[simp] lemma xorGatesAt_length (o a b : ℕ) : (xorGatesAt o a b).length = 5 := rfl

theorem encodeGates_xorGatesAt (o a b : ℕ) :
    (xorGatesAt o a b).flatMap QCSD_encodeGate = encodeXorAt o a b := by
  simp [xorGatesAt, encodeXorAt, List.append_assoc]

theorem emitXor_eq (gs : List QCSD_Gate) (a b : ℕ) :
    emitXor gs a b = (gs ++ xorGatesAt gs.length a b, gs.length + 4) := rfl

theorem encodeGates_emitXor (gs : List QCSD_Gate) (a b : ℕ) :
    (emitXor gs a b).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++ encodeXorAt gs.length a b := by
  rw [emitXor_eq, List.flatMap_append, encodeGates_xorGatesAt]

/-- The 6-gate XNOR (`==`) gadget emitted starting at wire offset `o = gs.length`. -/
def eqGatesAt (o a b : ℕ) : List QCSD_Gate :=
  xorGatesAt o a b ++ [⟨QCSD_GateOp.neg, o + 4, 0⟩]

/-- Exact bit-stream emitted by `eqGatesAt o a b`. -/
def encodeEqAt (o a b : ℕ) : List Bool :=
  encodeXorAt o a b ++ [false, true, true] ++ QCSD_natToUnary (o + 4)

@[simp] lemma eqGatesAt_length (o a b : ℕ) : (eqGatesAt o a b).length = 6 := rfl

theorem encodeGates_eqGatesAt (o a b : ℕ) :
    (eqGatesAt o a b).flatMap QCSD_encodeGate = encodeEqAt o a b := by
  simp [eqGatesAt, encodeEqAt, encodeGates_xorGatesAt, List.append_assoc]

theorem emitEq_eq (gs : List QCSD_Gate) (a b : ℕ) :
    emitEq gs a b = (gs ++ eqGatesAt gs.length a b, gs.length + 5) := by
  unfold emitEq emitNeg
  rw [emitXor_eq]
  simp [eqGatesAt, List.append_assoc]

theorem encodeGates_emitEq (gs : List QCSD_Gate) (a b : ℕ) :
    (emitEq gs a b).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++ encodeEqAt gs.length a b := by
  rw [emitEq_eq, List.flatMap_append, encodeGates_eqGatesAt]

theorem encodeGates_emitConst (gs : List QCSD_Gate) (b : Bool) :
    (emitConst gs b).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++ (if b then [false, false, true] else [false, true, false]) := by
  unfold emitConst
  rw [List.flatMap_append]
  simp [encodeGate_constBool]

theorem encodeGates_emitInput (gs : List QCSD_Gate) (i : ℕ) :
    (emitInput gs i).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++ ([false, false, false] ++ QCSD_natToUnary i) := by
  simp [emitInput]

theorem encodeGates_emitNeg (gs : List QCSD_Gate) (a : ℕ) :
    (emitNeg gs a).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++ ([false, true, true] ++ QCSD_natToUnary a) := by
  simp [emitNeg]

theorem encodeGates_emitConj (gs : List QCSD_Gate) (a b : ℕ) :
    (emitConj gs a b).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++
      ([true, false, false] ++ QCSD_natToUnary a ++ QCSD_natToUnary b) := by
  simp [emitConj]

theorem encodeGates_emitDisj (gs : List QCSD_Gate) (a b : ℕ) :
    (emitDisj gs a b).1.flatMap QCSD_encodeGate =
      gs.flatMap QCSD_encodeGate ++
      ([true, false, true] ++ QCSD_natToUnary a ++ QCSD_natToUnary b) := by
  simp [emitDisj]

theorem encodeGates_initInputs (numIn : ℕ) :
    (initInputs numIn).flatMap QCSD_encodeGate =
      (List.range numIn).flatMap (fun i => [false, false, false] ++ QCSD_natToUnary i) := by
  unfold initInputs
  rw [List.flatMap_map]
  rfl

@[simp] lemma initInputs_length (numIn : ℕ) : (initInputs numIn).length = numIn := by
  simp [initInputs]

@[simp] lemma emitConst_fst_len (gs : List QCSD_Gate) (b : Bool) :
    (emitConst gs b).1.length = gs.length + 1 := by simp [emitConst]
@[simp] lemma emitConst_snd (gs : List QCSD_Gate) (b : Bool) :
    (emitConst gs b).2 = gs.length := rfl

@[simp] lemma emitNeg_fst_len (gs : List QCSD_Gate) (a : ℕ) :
    (emitNeg gs a).1.length = gs.length + 1 := by simp [emitNeg]
@[simp] lemma emitNeg_snd (gs : List QCSD_Gate) (a : ℕ) :
    (emitNeg gs a).2 = gs.length := rfl

@[simp] lemma emitConj_fst_len (gs : List QCSD_Gate) (a b : ℕ) :
    (emitConj gs a b).1.length = gs.length + 1 := by simp [emitConj]
@[simp] lemma emitConj_snd (gs : List QCSD_Gate) (a b : ℕ) :
    (emitConj gs a b).2 = gs.length := rfl

@[simp] lemma emitDisj_fst_len (gs : List QCSD_Gate) (a b : ℕ) :
    (emitDisj gs a b).1.length = gs.length + 1 := by simp [emitDisj]
@[simp] lemma emitDisj_snd (gs : List QCSD_Gate) (a b : ℕ) :
    (emitDisj gs a b).2 = gs.length := rfl

@[simp] lemma emitXor_fst_len (gs : List QCSD_Gate) (a b : ℕ) :
    (emitXor gs a b).1.length = gs.length + 5 := by simp [emitXor]
@[simp] lemma emitXor_snd (gs : List QCSD_Gate) (a b : ℕ) :
    (emitXor gs a b).2 = gs.length + 4 := rfl

@[simp] lemma emitEq_fst_len (gs : List QCSD_Gate) (a b : ℕ) :
    (emitEq gs a b).1.length = gs.length + 6 := by simp [emitEq_eq]
@[simp] lemma emitEq_snd (gs : List QCSD_Gate) (a b : ℕ) :
    (emitEq gs a b).2 = gs.length + 5 := by simp [emitEq_eq]

@[simp] lemma encodeXorAt_length (o a b : ℕ) :
    (encodeXorAt o a b).length = 2 * a + 2 * b + 4 * o + 29 := by
  simp only [encodeXorAt, List.length_append, List.length_cons, List.length_nil, natToUnary_length]
  omega

@[simp] lemma encodeEqAt_length (o a b : ℕ) :
    (encodeEqAt o a b).length = 2 * a + 2 * b + 5 * o + 37 := by
  simp only [encodeEqAt, List.length_append, List.length_cons, List.length_nil,
    encodeXorAt_length, natToUnary_length]
  omega

lemma flatMap_flatMap_eq {α β γ : Type*} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap (fun a => (f a).flatMap g) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, List.flatMap_append, ih]

/-!
## Section 3: Explicit Imperative Loop & Wire-Index Formulas (`linearMapCheckCircuit` & `bilinearMapCheckCircuit`)
-/

/-- Number of active indices `t < k` satisfying `pred t = true`. -/
def prefixHits (pred : ℕ → Bool) (k : ℕ) : ℕ :=
  ((List.range k).filter pred).length

@[simp] theorem prefixHits_zero (pred : ℕ → Bool) : prefixHits pred 0 = 0 := rfl

theorem prefixHits_succ (pred : ℕ → Bool) (k : ℕ) :
    prefixHits pred (k + 1) = prefixHits pred k + if pred k then 1 else 0 := by
  unfold prefixHits
  rw [List.range_succ, List.filter_append, List.length_append]
  cases hk : pred k <;> simp [hk]

theorem prefixHits_le (pred : ℕ → Bool) (k : ℕ) : prefixHits pred k ≤ k := by
  unfold prefixHits
  exact (List.length_filter_le pred (List.range k)).trans (by simp)

lemma emitXorListAux_append (ws1 ws2 : List ℕ) :
    ∀ (gs : List QCSD_Gate) (acc : ℕ),
      emitXorListAux gs acc (ws1 ++ ws2) =
        let r1 := emitXorListAux gs acc ws1
        emitXorListAux r1.1 r1.2 ws2 := by
  induction ws1 with
  | nil => intro gs acc; rfl
  | cons w ws ih =>
    intro gs acc
    simp only [List.cons_append, emitXorListAux]
    exact ih _ _

lemma rowXorGates_length (base M : ℕ) (pred : ℕ → Bool) (inWire : ℕ → ℕ) :
    ((List.range M).flatMap (fun k =>
      if pred k then
        let acc := base + 5 * prefixHits pred k
        xorGatesAt (acc + 1) acc (inWire k)
      else [])).length = 5 * prefixHits pred M := by
  induction M with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, prefixHits_succ]
    cases hm : pred m
    · simp [hm]
    · simp [hm]; omega

/-- Exact imperative gate-stream and output-wire formula for `emitXorList` over a filtered range. -/
theorem emitXorList_filter_map_range (gs : List QCSD_Gate) (M : ℕ)
    (pred : ℕ → Bool) (inWire : ℕ → ℕ) :
    emitXorList gs (((List.range M).filter pred).map inWire) =
      (gs ++ [⟨QCSD_GateOp.ff, 0, 0⟩] ++
       (List.range M).flatMap (fun k =>
         if pred k then
           let acc := gs.length + 5 * prefixHits pred k
           xorGatesAt (acc + 1) acc (inWire k)
         else []),
       gs.length + 5 * prefixHits pred M) := by
  unfold emitXorList emitConst
  dsimp only
  induction M with
  | zero =>
    simp [emitXorListAux]
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.map_append, emitXorListAux_append, ih]
    dsimp only
    cases hm : pred m with
    | false =>
      simp [hm, emitXorListAux, prefixHits_succ]
    | true =>
      simp only [List.filter_cons_of_pos hm, List.filter_nil, List.map_cons, List.map_nil,
        emitXorListAux, emitXor_eq]
      have hlen :
          (gs ++ ([⟨QCSD_GateOp.ff, 0, 0⟩] : List QCSD_Gate) ++
           (List.range m).flatMap (fun k =>
             if pred k then
               let acc := gs.length + 5 * prefixHits pred k
               xorGatesAt (acc + 1) acc (inWire k)
             else [])).length =
          gs.length + 5 * prefixHits pred m + 1 := by
        rw [List.length_append, List.length_append, List.length_singleton,
            rowXorGates_length gs.length m pred inWire]
        omega
      rw [hlen]
      apply Prod.ext
      · simp [hm, List.append_assoc]
      · simp [prefixHits_succ, hm]
        omega

theorem emitXorList_filter_range (gs : List QCSD_Gate) (M : ℕ) (pred : ℕ → Bool) :
    emitXorList gs ((List.range M).filter pred) =
      (gs ++ [⟨QCSD_GateOp.ff, 0, 0⟩] ++
       (List.range M).flatMap (fun k =>
         if pred k then
           let acc := gs.length + 5 * prefixHits pred k
           xorGatesAt (acc + 1) acc k
         else []),
       gs.length + 5 * prefixHits pred M) := by
  have hmap : ((List.range M).filter pred).map id = (List.range M).filter pred := List.map_id _
  rw [← hmap, emitXorList_filter_map_range]
  rfl

/-- Active input count in parity-check row `j`. -/
def parityRowHits (M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) : ℕ :=
  prefixHits (active j) M

/-- Exact wire index `curWire` at the start of parity-check row `j` (starting from `base` at `j = 0`). -/
def parityRowStart (base M : ℕ) (active : ℕ → ℕ → Bool) : ℕ → ℕ
  | 0 => base
  | j + 1 => parityRowStart base M active j + 7 + 5 * parityRowHits M active j

/-- Exact output equality wire index produced at the end of parity-check row `j`. -/
def parityEqWire (base M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) : ℕ :=
  parityRowStart base M active j + 6 + 5 * parityRowHits M active j

@[simp] theorem parityRowStart_zero (base M : ℕ) (active : ℕ → ℕ → Bool) :
    parityRowStart base M active 0 = base := rfl

@[simp] theorem parityRowStart_succ (base M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) :
    parityRowStart base M active (j + 1) =
      parityRowStart base M active j + 7 + 5 * parityRowHits M active j := rfl

theorem parityEqWire_add_one (base M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) :
    parityEqWire base M active j + 1 = parityRowStart base M active (j + 1) := by
  rw [parityRowStart_succ]
  unfold parityEqWire
  omega

/-- Closed-form sum formula for `parityRowStart` across `R` rows. -/
theorem parityRowStart_eq_sum (base M : ℕ) (active : ℕ → ℕ → Bool) (R : ℕ) :
    parityRowStart base M active R =
      base + 7 * R + 5 * ((List.range R).map (parityRowHits M active)).sum := by
  induction R with
  | zero => simp
  | succ r ih =>
    rw [parityRowStart_succ, ih, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    omega

/-- Step-by-step inner wire-counter recurrence inside row `j` before column `k`. -/
def parityInnerWire (base M : ℕ) (active : ℕ → ℕ → Bool) (j k : ℕ) : ℕ :=
  parityRowStart base M active j + 1 + 5 * prefixHits (active j) k

@[simp] theorem parityInnerWire_zero (base M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) :
    parityInnerWire base M active j 0 = parityRowStart base M active j + 1 := by
  simp [parityInnerWire]

theorem parityInnerWire_succ (base M : ℕ) (active : ℕ → ℕ → Bool) (j k : ℕ) :
    parityInnerWire base M active j (k + 1) =
      parityInnerWire base M active j k + (if active j k then 5 else 0) := by
  unfold parityInnerWire
  rw [prefixHits_succ]
  cases active j k
  · simp
  · simp; omega

theorem parityInnerWire_end (base M : ℕ) (active : ℕ → ℕ → Bool) (j : ℕ) :
    parityInnerWire base M active j M =
      parityRowStart base M active j + 1 + 5 * parityRowHits M active j := rfl

/-- Gates emitted during row `j` of `emitParityChecks`. -/
def parityRowGates (base M : ℕ) (outWire inWire : ℕ → ℕ)
    (active : ℕ → ℕ → Bool) (j : ℕ) : List QCSD_Gate :=
  let rBase := parityRowStart base M active j
  let endXorAcc := rBase + 5 * parityRowHits M active j
  [⟨QCSD_GateOp.ff, 0, 0⟩] ++
  (List.range M).flatMap (fun k =>
    if active j k then
      let acc := rBase + 5 * prefixHits (active j) k
      xorGatesAt (acc + 1) acc (inWire k)
    else []) ++
  eqGatesAt (endXorAcc + 1) (outWire j) endXorAcc

/-- Exact encoded `List Bool` emitted during row `j` of `emitParityChecks`. -/
def encodeParityRow (base M : ℕ) (outWire inWire : ℕ → ℕ)
    (active : ℕ → ℕ → Bool) (j : ℕ) : List Bool :=
  let rBase := parityRowStart base M active j
  let endXorAcc := rBase + 5 * parityRowHits M active j
  [false, true, false] ++
  (List.range M).flatMap (fun k =>
    if active j k then
      let acc := rBase + 5 * prefixHits (active j) k
      encodeXorAt (acc + 1) acc (inWire k)
    else []) ++
  encodeEqAt (endXorAcc + 1) (outWire j) endXorAcc

lemma parityRowGates_length (base M : ℕ) (outWire inWire : ℕ → ℕ)
    (active : ℕ → ℕ → Bool) (j : ℕ) :
    (parityRowGates base M outWire inWire active j).length =
      7 + 5 * parityRowHits M active j := by
  unfold parityRowGates parityRowHits
  dsimp only
  rw [List.length_append, List.length_append, List.length_singleton,
      rowXorGates_length _ M (active j) inWire, eqGatesAt_length]
  omega

theorem encodeGates_parityRowGates (base M : ℕ) (outWire inWire : ℕ → ℕ)
    (active : ℕ → ℕ → Bool) (j : ℕ) :
    (parityRowGates base M outWire inWire active j).flatMap QCSD_encodeGate =
      encodeParityRow base M outWire inWire active j := by
  unfold parityRowGates encodeParityRow
  dsimp only
  rw [List.flatMap_append, List.flatMap_append, encodeGates_eqGatesAt]
  congr 1
  congr 1
  rw [flatMap_flatMap_eq]
  refine List.flatMap_congr (fun k _ => ?_)
  cases active j k
  · simp
  · simp [encodeGates_xorGatesAt]

lemma parityRowsPrefix_length (base M : ℕ) (outWire inWire : ℕ → ℕ)
    (active : ℕ → ℕ → Bool) (R : ℕ) :
    base + ((List.range R).flatMap (parityRowGates base M outWire inWire active)).length =
      parityRowStart base M active R := by
  induction R with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton,
        parityRowGates_length, parityRowStart_succ]
    omega

lemma emitParityChecks_append (s1 s2 : List (ℕ × List ℕ)) :
    ∀ (gs : List QCSD_Gate),
      emitParityChecks gs (s1 ++ s2) =
        let r1 := emitParityChecks gs s1
        let r2 := emitParityChecks r1.1 s2
        (r2.1, r1.2 ++ r2.2) := by
  induction s1 with
  | nil => intro gs; simp [emitParityChecks]
  | cons p ps ih =>
    rcases p with ⟨outW, inWs⟩
    intro gs
    simp only [List.cons_append, emitParityChecks]
    rw [ih]

/-- Exact imperative gate-stream and equality-wire list for `emitParityChecks`. -/
theorem emitParityChecks_range (gs : List QCSD_Gate) (R M : ℕ)
    (outWire inWire : ℕ → ℕ) (active : ℕ → ℕ → Bool) :
    emitParityChecks gs ((List.range R).map (fun j =>
      (outWire j, ((List.range M).filter (active j)).map inWire))) =
    (gs ++ (List.range R).flatMap (parityRowGates gs.length M outWire inWire active),
     (List.range R).map (parityEqWire gs.length M active)) := by
  induction R with
  | zero =>
    simp [emitParityChecks]
  | succ r ih =>
    rw [List.range_succ, List.map_append, emitParityChecks_append, ih]
    dsimp only
    simp only [List.map_singleton, emitParityChecks]
    have hcur_len :
        (gs ++ (List.range r).flatMap (parityRowGates gs.length M outWire inWire active)).length =
          parityRowStart gs.length M active r := by
      rw [List.length_append]
      exact parityRowsPrefix_length gs.length M outWire inWire active r
    rw [emitXorList_filter_map_range, hcur_len, emitEq_eq]
    have hrx_len :
        (gs ++ (List.range r).flatMap (parityRowGates gs.length M outWire inWire active) ++
         ([⟨QCSD_GateOp.ff, 0, 0⟩] : List QCSD_Gate) ++
         (List.range M).flatMap (fun k =>
           if active r k then
             let acc := parityRowStart gs.length M active r + 5 * prefixHits (active r) k
             xorGatesAt (acc + 1) acc (inWire k)
           else [])).length =
        parityRowStart gs.length M active r + 5 * parityRowHits M active r + 1 := by
      rw [List.length_append, List.length_append, hcur_len, List.length_singleton,
          rowXorGates_length _ M (active r) inWire]
      unfold parityRowHits
      omega
    rw [hrx_len]
    apply Prod.ext
    · simp only [List.flatMap_append, List.flatMap_singleton]
      unfold parityRowGates parityRowHits
      simp [List.append_assoc]
    · simp only [List.map_append, List.map_singleton]
      unfold parityEqWire parityRowHits
      congr 1
      congr 1
      omega

lemma emitAllAux_append (ws1 ws2 : List ℕ) :
    ∀ (gs : List QCSD_Gate) (acc : ℕ),
      emitAllAux gs acc (ws1 ++ ws2) =
        let r1 := emitAllAux gs acc ws1
        emitAllAux r1.1 r1.2 ws2 := by
  induction ws1 with
  | nil => intro gs acc; rfl
  | cons w ws ih =>
    intro gs acc
    simp only [List.cons_append, emitAllAux]
    exact ih _ _

/-- Exact imperative gate-stream and output-wire formula for `emitAll` over `(List.range R).map eqWire`. -/
theorem emitAll_map_range (gs : List QCSD_Gate) (R : ℕ) (eqWire : ℕ → ℕ) :
    emitAll gs ((List.range R).map eqWire) =
      (gs ++ [⟨QCSD_GateOp.tt, 0, 0⟩] ++
       (List.range R).map (fun j => ⟨QCSD_GateOp.conj, gs.length + j, eqWire j⟩),
       gs.length + R) := by
  unfold emitAll emitConst
  dsimp only
  induction R with
  | zero =>
    simp [emitAllAux]
  | succ r ih =>
    rw [List.range_succ, List.map_append, emitAllAux_append, ih]
    dsimp only
    simp only [List.map_singleton, emitAllAux, emitConj]
    have hlen :
        (gs ++ ([⟨QCSD_GateOp.tt, 0, 0⟩] : List QCSD_Gate) ++
         (List.range r).map (fun j => (⟨QCSD_GateOp.conj, gs.length + j, eqWire j⟩ : QCSD_Gate))).length =
        gs.length + (r + 1) := by
      simp
    rw [hlen]
    apply Prod.ext
    · simp [List.append_assoc]
    · rfl

/-- Exact gate-stream formula for `emitPairConjs`. -/
theorem emitPairConjs_eq_append (pairs : List (ℕ × ℕ)) :
    ∀ (gs : List QCSD_Gate),
      emitPairConjs gs pairs = gs ++ pairs.map (fun p => ⟨QCSD_GateOp.conj, p.1, p.2⟩) := by
  induction pairs with
  | nil => intro gs; simp [emitPairConjs]
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    intro gs
    simp only [emitPairConjs, emitConj, ih, List.map_cons, List.append_assoc, List.singleton_append]

theorem emitPairConjs_bilinearPairs (gs : List QCSD_Gate) (n1 n2 : ℕ) :
    emitPairConjs gs (bilinearPairs n1 n2) =
      gs ++ (List.range (n1 * n2)).map (fun k => ⟨QCSD_GateOp.conj, k / n2, n1 + k % n2⟩) := by
  rw [emitPairConjs_eq_append]
  simp [bilinearPairs, List.map_map]

/-- Exact gate list of `linearMapCheckCircuit numIn numOut mat` as sequential `List.range` loops. -/
theorem linearMapCheckCircuit_gates_eq (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) :
    let totalIn := numIn + numOut
    let allBase := parityRowStart totalIn numIn mat numOut
    (linearMapCheckCircuit numIn numOut mat).gates =
      initInputs totalIn ++
      (List.range numOut).flatMap (parityRowGates totalIn numIn (fun j => numIn + j) id mat) ++
      [⟨QCSD_GateOp.tt, 0, 0⟩] ++
      (List.range numOut).map (fun j =>
        ⟨QCSD_GateOp.conj, allBase + j, parityEqWire totalIn numIn mat j⟩) := by
  unfold linearMapCheckCircuit
  dsimp only
  have hspecs :
      (List.range numOut).map (fun j => (numIn + j, (List.range numIn).filter (fun i => mat j i))) =
      (List.range numOut).map (fun j => (numIn + j, ((List.range numIn).filter (mat j)).map id)) := by
    refine List.map_congr_left (fun j _ => ?_)
    simp
  rw [hspecs, emitParityChecks_range, emitAll_map_range]
  dsimp only
  have hlen0 : (initInputs (numIn + numOut)).length = numIn + numOut := initInputs_length _
  have hlen_pc :
      (initInputs (numIn + numOut) ++
       (List.range numOut).flatMap
         (parityRowGates (initInputs (numIn + numOut)).length numIn (fun j => numIn + j) id mat)).length =
      parityRowStart (numIn + numOut) numIn mat numOut := by
    rw [List.length_append, hlen0]
    exact parityRowsPrefix_length (numIn + numOut) numIn (fun j => numIn + j) id mat numOut
  rw [hlen_pc, hlen0]

/-- Exact gate count of `linearMapCheckCircuit numIn numOut mat`. -/
theorem linearMapCheckCircuit_gates_length (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) :
    (linearMapCheckCircuit numIn numOut mat).gates.length =
      parityRowStart (numIn + numOut) numIn mat numOut + 1 + numOut := by
  rw [linearMapCheckCircuit_gates_eq]
  have hpc := parityRowsPrefix_length (numIn + numOut) numIn (fun j => numIn + j) id mat numOut
  simp only [List.length_append, initInputs_length, List.length_singleton, List.length_map,
    List.length_range]
  omega

/-- **Explicit Imperative Loop Bit-Stream Formula for `linearMapCheckCircuit`**:
expresses `QCSD_encodeCircuit (linearMapCheckCircuit numIn numOut mat)` purely via sequential
`List.range` loops and closed-form wire indices (`parityRowStart`, `prefixHits`, `parityEqWire`). -/
theorem encodeCircuit_linearMapCheckCircuit (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) :
    let totalIn := numIn + numOut
    let allBase := parityRowStart totalIn numIn mat numOut
    QCSD_encodeCircuit (linearMapCheckCircuit numIn numOut mat) =
      QCSD_natToUnary totalIn ++
      QCSD_natToUnary (allBase + 1 + numOut) ++
      (List.range totalIn).flatMap (fun i =>
        [false, false, false] ++ QCSD_natToUnary i) ++
      (List.range numOut).flatMap (fun j =>
        encodeParityRow totalIn numIn (fun r => numIn + r) id mat j) ++
      [false, false, true] ++
      (List.range numOut).flatMap (fun j =>
        [true, false, false] ++
        QCSD_natToUnary (allBase + j) ++
        QCSD_natToUnary (parityEqWire totalIn numIn mat j)) := by
  dsimp only
  unfold QCSD_encodeCircuit
  have hnum : (linearMapCheckCircuit numIn numOut mat).numInputs = numIn + numOut := rfl
  rw [hnum, linearMapCheckCircuit_gates_length, linearMapCheckCircuit_gates_eq]
  simp only [List.flatMap_append, encodeGates_initInputs, List.flatMap_singleton, encodeGate_tt,
    List.flatMap_map, encodeGate_conj, List.append_assoc]
  congr 1
  congr 1
  congr 1
  rw [flatMap_flatMap_eq]
  congr 1
  exact List.flatMap_congr (fun j _ =>
    encodeGates_parityRowGates (numIn + numOut) numIn (fun r => numIn + r) id mat j)

/-- Exact gate list of `bilinearMapCheckCircuit n1 n2 nOut tensor` as sequential `List.range` loops. -/
theorem bilinearMapCheckCircuit_gates_eq (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) :
    let totalIn := n1 + n2 + nOut
    let pairBase := totalIn + n1 * n2
    let active := fun j k => tensor j (k / n2) (k % n2)
    let allBase := parityRowStart pairBase (n1 * n2) active nOut
    (bilinearMapCheckCircuit n1 n2 nOut tensor).gates =
      initInputs totalIn ++
      (List.range (n1 * n2)).map (fun k => ⟨QCSD_GateOp.conj, k / n2, n1 + k % n2⟩) ++
      (List.range nOut).flatMap
        (parityRowGates pairBase (n1 * n2) (fun j => n1 + n2 + j) (fun k => totalIn + k) active) ++
      [⟨QCSD_GateOp.tt, 0, 0⟩] ++
      (List.range nOut).map (fun j =>
        ⟨QCSD_GateOp.conj, allBase + j, parityEqWire pairBase (n1 * n2) active j⟩) := by
  unfold bilinearMapCheckCircuit
  dsimp only
  rw [emitPairConjs_bilinearPairs, emitParityChecks_range, emitAll_map_range]
  dsimp only
  set totalIn := n1 + n2 + nOut
  set gs1 := initInputs totalIn ++
    (List.range (n1 * n2)).map (fun k => ⟨QCSD_GateOp.conj, k / n2, n1 + k % n2⟩)
  have hlen1 : gs1.length = totalIn + n1 * n2 := by simp [gs1]
  have hlen_pc :
      (gs1 ++
       (List.range nOut).flatMap
         (parityRowGates gs1.length (n1 * n2) (fun j => n1 + n2 + j) (fun k => totalIn + k)
           (fun j k => tensor j (k / n2) (k % n2)))).length =
      parityRowStart (totalIn + n1 * n2) (n1 * n2) (fun j k => tensor j (k / n2) (k % n2)) nOut := by
    rw [List.length_append, hlen1]
    exact parityRowsPrefix_length (totalIn + n1 * n2) (n1 * n2)
      (fun j => n1 + n2 + j) (fun k => totalIn + k) (fun j k => tensor j (k / n2) (k % n2)) nOut
  rw [hlen_pc, hlen1]

/-- Exact gate count of `bilinearMapCheckCircuit n1 n2 nOut tensor`. -/
theorem bilinearMapCheckCircuit_gates_length (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) :
    let pairBase := (n1 + n2 + nOut) + n1 * n2
    let active := fun j k => tensor j (k / n2) (k % n2)
    (bilinearMapCheckCircuit n1 n2 nOut tensor).gates.length =
      parityRowStart pairBase (n1 * n2) active nOut + 1 + nOut := by
  dsimp only
  rw [bilinearMapCheckCircuit_gates_eq]
  have hpc := parityRowsPrefix_length ((n1 + n2 + nOut) + n1 * n2) (n1 * n2)
    (fun j => n1 + n2 + j) (fun k => (n1 + n2 + nOut) + k)
    (fun j k => tensor j (k / n2) (k % n2)) nOut
  simp only [List.length_append, initInputs_length, List.length_map, List.length_range,
    List.length_singleton]
  omega

/-- **Explicit Imperative Loop Bit-Stream Formula for `bilinearMapCheckCircuit`**:
expresses `QCSD_encodeCircuit (bilinearMapCheckCircuit n1 n2 nOut tensor)` purely via sequential
`List.range` loops and closed-form wire indices. -/
theorem encodeCircuit_bilinearMapCheckCircuit (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) :
    let totalIn := n1 + n2 + nOut
    let pairBase := totalIn + n1 * n2
    let active := fun j k => tensor j (k / n2) (k % n2)
    let allBase := parityRowStart pairBase (n1 * n2) active nOut
    QCSD_encodeCircuit (bilinearMapCheckCircuit n1 n2 nOut tensor) =
      QCSD_natToUnary totalIn ++
      QCSD_natToUnary (allBase + 1 + nOut) ++
      (List.range totalIn).flatMap (fun i =>
        [false, false, false] ++ QCSD_natToUnary i) ++
      (List.range (n1 * n2)).flatMap (fun k =>
        [true, false, false] ++
        QCSD_natToUnary (k / n2) ++
        QCSD_natToUnary (n1 + k % n2)) ++
      (List.range nOut).flatMap (fun j =>
        encodeParityRow pairBase (n1 * n2)
          (fun r => n1 + n2 + r) (fun k => totalIn + k) active j) ++
      [false, false, true] ++
      (List.range nOut).flatMap (fun j =>
        [true, false, false] ++
        QCSD_natToUnary (allBase + j) ++
        QCSD_natToUnary (parityEqWire pairBase (n1 * n2) active j)) := by
  dsimp only
  unfold QCSD_encodeCircuit
  have hnum : (bilinearMapCheckCircuit n1 n2 nOut tensor).numInputs = n1 + n2 + nOut := rfl
  rw [hnum, bilinearMapCheckCircuit_gates_length, bilinearMapCheckCircuit_gates_eq]
  simp only [List.flatMap_append, encodeGates_initInputs, List.flatMap_singleton, encodeGate_tt,
    List.flatMap_map, encodeGate_conj, List.append_assoc]
  congr 1
  congr 1
  congr 1
  congr 1
  rw [flatMap_flatMap_eq]
  congr 1
  exact List.flatMap_congr (fun j _ =>
    encodeGates_parityRowGates ((n1 + n2 + nOut) + n1 * n2) (n1 * n2)
      (fun r => n1 + n2 + r) (fun k => (n1 + n2 + nOut) + k)
      (fun j k => tensor j (k / n2) (k % n2)) j)

/-- Division-free nested loop helper: splits `List.range (n1 * n2)` into `i1 < n1` and `i2 < n2`. -/
lemma range_mul_eq_flatMap (n1 n2 : ℕ) :
    List.range (n1 * n2) =
      (List.range n1).flatMap (fun i1 => (List.range n2).map (fun i2 => i1 * n2 + i2)) := by
  induction n1 with
  | zero => simp
  | succ m ih =>
    have hmul : (m + 1) * n2 = m * n2 + n2 := by ring
    rw [hmul, List.range_add, ih, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Division-free nested loop rewrite for the `n1 * n2` pairwise-conjunction stream when `0 < n2`. -/
theorem encodePairConjs_nested_loop (n1 n2 : ℕ) (hn2 : 0 < n2) :
    (List.range (n1 * n2)).flatMap (fun k =>
      [true, false, false] ++ QCSD_natToUnary (k / n2) ++ QCSD_natToUnary (n1 + k % n2)) =
    (List.range n1).flatMap (fun i1 =>
      (List.range n2).flatMap (fun i2 =>
        [true, false, false] ++ QCSD_natToUnary i1 ++ QCSD_natToUnary (n1 + i2))) := by
  rw [range_mul_eq_flatMap n1 n2, flatMap_flatMap_eq]
  refine List.flatMap_congr (fun i1 _ => ?_)
  rw [List.flatMap_map]
  refine List.flatMap_congr (fun i2 hi2 => ?_)
  have hi2_lt : i2 < n2 := List.mem_range.mp hi2
  have hdiv : (i1 * n2 + i2) / n2 = i1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn2, Nat.div_eq_of_lt hi2_lt, Nat.zero_add]
  have hmod : (i1 * n2 + i2) % n2 = i2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi2_lt]
  rw [hdiv, hmod]

/-!
## Section 4: Concrete Small-Circuit Bit-Literal & Closed-Form `List Bool` Lemmas
-/

/-! ### 4.1 `constCircuit` -/

theorem encodeCircuit_constCircuit (numIn : ℕ) (b : Bool) :
    QCSD_encodeCircuit (constCircuit numIn b) =
      QCSD_natToUnary numIn ++ [true, false] ++
        (if b then [false, false, true] else [false, true, false]) := by
  cases b <;> simp [constCircuit, QCSD_encodeCircuit, QCSD_natToUnary, List.append_assoc]

@[simp] theorem encodeCircuit_constCircuit_length (numIn : ℕ) (b : Bool) :
    (QCSD_encodeCircuit (constCircuit numIn b)).length = numIn + 6 := by
  rw [encodeCircuit_constCircuit]
  cases b <;> simp

theorem encodeCircuit_constCircuit_0_false :
    QCSD_encodeCircuit (constCircuit 0 false) = [false, true, false, false, true, false] := rfl

theorem encodeCircuit_constCircuit_0_true :
    QCSD_encodeCircuit (constCircuit 0 true) = [false, true, false, false, false, true] := rfl

theorem encodeCircuit_constCircuit_1_false :
    QCSD_encodeCircuit (constCircuit 1 false) =
      [true, false, true, false, false, true, false] := rfl

theorem encodeCircuit_constCircuit_1_true :
    QCSD_encodeCircuit (constCircuit 1 true) =
      [true, false, true, false, false, false, true] := rfl

theorem encodeCircuit_constCircuit_3_false :
    QCSD_encodeCircuit (constCircuit 3 false) =
      [true, true, true, false, true, false, false, true, false] := rfl

theorem encodeCircuit_constCircuit_5_false :
    QCSD_encodeCircuit (constCircuit 5 false) =
      [true, true, true, true, true, false, true, false, false, true, false] := rfl

/-! ### 4.2 `pinBitCircuit` -/

theorem encodeCircuit_pinBitCircuit_none :
    QCSD_encodeCircuit (pinBitCircuit none) =
      [true, false, true, false, false, false, true] := rfl

theorem encodeCircuit_pinBitCircuit_some_true :
    QCSD_encodeCircuit (pinBitCircuit (some true)) =
      [true, false, true, false, false, false, false, false] := rfl

theorem encodeCircuit_pinBitCircuit_some_false :
    QCSD_encodeCircuit (pinBitCircuit (some false)) =
      [true, false, true, true, false, false, false, false, false, false, true, true, false] := rfl

theorem encodeCircuit_pinBitCircuit (opt : Option Bool) :
    QCSD_encodeCircuit (pinBitCircuit opt) =
      match opt with
      | none => [true, false, true, false, false, false, true]
      | some true => [true, false, true, false, false, false, false, false]
      | some false =>
        [true, false, true, true, false, false, false, false, false, false, true, true, false] := by
  cases opt with
  | none => rfl
  | some b => cases b <;> rfl

/-! ### 4.3 `guardedBitCircuit` -/

theorem encodeCircuit_guardedBitCircuit_ff :
    QCSD_encodeCircuit (guardedBitCircuit false false) =
      [true, false, true, false, false, true, false] := rfl

theorem encodeCircuit_guardedBitCircuit_ft :
    QCSD_encodeCircuit (guardedBitCircuit false true) =
      [true, false, true, false, false, true, false] := rfl

theorem encodeCircuit_guardedBitCircuit_tf :
    QCSD_encodeCircuit (guardedBitCircuit true false) =
      [true, false, true, true, false, false, false, false, false, false, true, true, false] := rfl

theorem encodeCircuit_guardedBitCircuit_tt :
    QCSD_encodeCircuit (guardedBitCircuit true true) =
      [true, false, true, false, false, false, false, false] := rfl

theorem encodeCircuit_guardedBitCircuit (guard target : Bool) :
    QCSD_encodeCircuit (guardedBitCircuit guard target) =
      if guard then
        if target then [true, false, true, false, false, false, false, false]
        else [true, false, true, true, false, false, false, false, false, false, true, true, false]
      else [true, false, true, false, false, true, false] := by
  cases guard <;> cases target <;> rfl

/-! ### 4.4 `sepCmpStepCircuit`, `borrowStepCircuit`, `exactCmpStepCircuit` -/

theorem encodeCircuit_sepCmpStepCircuit :
    QCSD_encodeCircuit sepCmpStepCircuit =
      [true, true, true, false, true, true, false, false, false, false, true, true, false,
       false, true, true, false] := rfl

theorem encodeCircuit_sepCmpStepCircuit_length :
    (QCSD_encodeCircuit sepCmpStepCircuit).length = 17 := rfl

def borrowStepBits (tBit : Bool) : List Bool :=
  QCSD_natToUnary 3 ++ QCSD_natToUnary 10 ++
  [false, false, false, false, false, false, false, true, false, false, false, false, true, true, false] ++
  (if tBit then [true, false, false, false, true, false]
   else [true, false, true, false, true, false]) ++
  encodeEqAt 4 2 3

theorem encodeCircuit_borrowStepCircuit (tBit : Bool) :
    QCSD_encodeCircuit (borrowStepCircuit tBit) = borrowStepBits tBit := by
  cases tBit <;> rfl

theorem encodeCircuit_borrowStepCircuit_length (tBit : Bool) :
    (QCSD_encodeCircuit (borrowStepCircuit tBit)).length = 103 := by
  cases tBit <;> rfl

def exactCmpStepBits (guard tBit : Bool) : List Bool :=
  if !guard then
    [true, true, true, false, true, false, false, true, false]
  else
    QCSD_natToUnary 3 ++ QCSD_natToUnary 12 ++
    [false, false, false, false, false, false, false, true, false, false, false, false, true, true, false] ++
    (if tBit then [false, false, true] else [false, true, false]) ++
    encodeEqAt 4 0 3 ++
    [false, true, true, true, true, false] ++
    [true, false, false] ++ QCSD_natToUnary 9 ++ QCSD_natToUnary 10

theorem encodeCircuit_exactCmpStepCircuit (guard tBit : Bool) :
    QCSD_encodeCircuit (exactCmpStepCircuit guard tBit) = exactCmpStepBits guard tBit := by
  cases guard <;> cases tBit <;> rfl

theorem encodeCircuit_exactCmpStepCircuit_length (guard tBit : Bool) :
    (QCSD_encodeCircuit (exactCmpStepCircuit guard tBit)).length =
      if guard then 128 else 9 := by
  cases guard <;> cases tBit <;> rfl

/-! ### 4.5 `synCheckCircuit`, `fullAdderCircuit`, `sepFullAdderCircuit` -/

def synCheckBits (target : Bool) : List Bool :=
  QCSD_natToUnary 3 ++ QCSD_natToUnary 20 ++
  [false, false, false, false, false, false, false, true, false, false, false, false, true, true, false] ++
  encodeXorAt 3 0 1 ++
  encodeXorAt 8 7 2 ++
  (if target then [false, false, true] else [false, true, false]) ++
  encodeEqAt 14 12 13

theorem encodeCircuit_synCheckCircuit (target : Bool) :
    QCSD_encodeCircuit (synCheckCircuit target) = synCheckBits target := by
  simp only [synCheckCircuit, QCSD_encodeCircuit, synCheckBits,
    encodeGates_emitEq, encodeGates_emitConst, encodeGates_emitXor,
    emitEq_fst_len, emitConst_fst_len, emitConst_snd, emitXor_fst_len, emitXor_snd,
    List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
    encodeGate_input, List.append_assoc]
  cases target <;> rfl

theorem encodeCircuit_synCheckCircuit_length (target : Bool) :
    (QCSD_encodeCircuit (synCheckCircuit target)).length = 322 := by
  rw [encodeCircuit_synCheckCircuit]
  cases target <;> simp [synCheckBits]

def fullAdderGatesBits : List Bool :=
  [false, false, false] ++ QCSD_natToUnary 0 ++
  [false, false, false] ++ QCSD_natToUnary 1 ++
  [false, false, false] ++ QCSD_natToUnary 2 ++
  [false, false, false] ++ QCSD_natToUnary 3 ++
  [false, false, false] ++ QCSD_natToUnary 4 ++
  encodeXorAt 5 0 1 ++
  encodeXorAt 10 9 2 ++
  encodeEqAt 15 3 14 ++
  [true, false, false] ++ QCSD_natToUnary 0 ++ QCSD_natToUnary 1 ++
  [true, false, false] ++ QCSD_natToUnary 0 ++ QCSD_natToUnary 2 ++
  [true, false, false] ++ QCSD_natToUnary 1 ++ QCSD_natToUnary 2 ++
  [true, false, true] ++ QCSD_natToUnary 22 ++ QCSD_natToUnary 23 ++
  [true, false, true] ++ QCSD_natToUnary 21 ++ QCSD_natToUnary 24 ++
  encodeEqAt 26 4 25 ++
  [true, false, false] ++ QCSD_natToUnary 20 ++ QCSD_natToUnary 31

def fullAdderBits : List Bool :=
  QCSD_natToUnary 5 ++ QCSD_natToUnary 33 ++ fullAdderGatesBits

lemma fullAdderCircuit_gates_length : fullAdderCircuit.gates.length = 33 := by
  simp [fullAdderCircuit]

lemma encodeGates_fullAdderCircuit :
    fullAdderCircuit.gates.flatMap QCSD_encodeGate = fullAdderGatesBits := by
  simp only [fullAdderCircuit, fullAdderGatesBits,
    encodeGates_emitConj, encodeGates_emitEq, encodeGates_emitDisj, encodeGates_emitXor,
    emitConj_fst_len, emitConj_snd, emitDisj_fst_len, emitDisj_snd,
    emitEq_fst_len, emitEq_snd, emitXor_fst_len, emitXor_snd,
    List.flatMap_cons, List.flatMap_nil, List.length_cons, List.length_nil,
    encodeGate_input, List.append_assoc]
  rfl

theorem encodeCircuit_fullAdderCircuit :
    QCSD_encodeCircuit fullAdderCircuit = fullAdderBits := by
  unfold QCSD_encodeCircuit fullAdderBits
  have hnum : fullAdderCircuit.numInputs = 5 := rfl
  rw [hnum, fullAdderCircuit_gates_length, encodeGates_fullAdderCircuit]

theorem encodeCircuit_fullAdderCircuit_length :
    (QCSD_encodeCircuit fullAdderCircuit).length = 760 := by
  rw [encodeCircuit_fullAdderCircuit]
  simp [fullAdderBits, fullAdderGatesBits]

def sepFullAdderBits (guard t0Bit t1Bit : Bool) : List Bool :=
  if !guard then
    [true, true, true, true, true, false, true, false, false, true, false]
  else
    QCSD_natToUnary 5 ++ QCSD_natToUnary 49 ++
    fullAdderGatesBits ++
    (if t0Bit then [false, false, true] else [false, true, false]) ++
    encodeEqAt 34 0 33 ++
    (if t1Bit then [false, false, true] else [false, true, false]) ++
    encodeEqAt 41 1 40 ++
    [true, false, false] ++ QCSD_natToUnary 32 ++ QCSD_natToUnary 39 ++
    [true, false, false] ++ QCSD_natToUnary 47 ++ QCSD_natToUnary 46

theorem encodeCircuit_sepFullAdderCircuit (guard t0Bit t1Bit : Bool) :
    QCSD_encodeCircuit (sepFullAdderCircuit guard t0Bit t1Bit) =
      sepFullAdderBits guard t0Bit t1Bit := by
  cases guard with
  | false => rfl
  | true =>
    unfold sepFullAdderCircuit sepFullAdderBits QCSD_encodeCircuit
    have hnot : (!true) = false := rfl
    rw [hnot, ite_eq_right Bool.noConfusion, ite_eq_right Bool.noConfusion]
    dsimp only
    simp only [encodeGates_emitConj, encodeGates_emitEq, encodeGates_emitConst,
      emitConj_fst_len, emitConj_snd, emitEq_fst_len, emitEq_snd, emitConst_fst_len, emitConst_snd,
      fullAdderCircuit_gates_length, encodeGates_fullAdderCircuit, List.append_assoc]

theorem encodeCircuit_sepFullAdderCircuit_length (guard t0Bit t1Bit : Bool) :
    (QCSD_encodeCircuit (sepFullAdderCircuit guard t0Bit t1Bit)).length =
      if guard then 1553 else 11 := by
  rw [encodeCircuit_sepFullAdderCircuit]
  cases guard <;> cases t0Bit <;> cases t1Bit <;>
    simp [sepFullAdderBits, fullAdderGatesBits]

/-! ### 4.6 Fixed Small `linearMapCheckCircuit` Instances Used in `rawPred` (`v_ecopy` & `v_ovl`) -/

def ecopyBits : List Bool :=
  QCSD_natToUnary 3 ++ QCSD_natToUnary 30 ++
  [false, false, false] ++ QCSD_natToUnary 0 ++
  [false, false, false] ++ QCSD_natToUnary 1 ++
  [false, false, false] ++ QCSD_natToUnary 2 ++
  [false, true, false] ++ encodeXorAt 4 3 0 ++ encodeEqAt 9 1 8 ++
  [false, true, false] ++ encodeXorAt 16 15 0 ++ encodeEqAt 21 2 20 ++
  [false, false, true] ++
  [true, false, false] ++ QCSD_natToUnary 27 ++ QCSD_natToUnary 14 ++
  [true, false, false] ++ QCSD_natToUnary 28 ++ QCSD_natToUnary 26

theorem encodeCircuit_ecopy :
    QCSD_encodeCircuit (linearMapCheckCircuit 1 2 (fun _ _ => true)) = ecopyBits := by
  rw [encodeCircuit_linearMapCheckCircuit]
  simp [ecopyBits, encodeParityRow, parityRowStart, parityRowHits, parityEqWire, prefixHits,
    List.range_succ, List.append_assoc]

def ovl0Bits : List Bool :=
  QCSD_natToUnary 1 ++ QCSD_natToUnary 10 ++
  [false, false, false] ++ QCSD_natToUnary 0 ++
  [false, true, false] ++ encodeEqAt 2 0 1 ++
  [false, false, true] ++
  [true, false, false] ++ QCSD_natToUnary 8 ++ QCSD_natToUnary 7

def ovl1Bits : List Bool :=
  QCSD_natToUnary 2 ++ QCSD_natToUnary 16 ++
  [false, false, false] ++ QCSD_natToUnary 0 ++
  [false, false, false] ++ QCSD_natToUnary 1 ++
  [false, true, false] ++ encodeXorAt 3 2 0 ++ encodeEqAt 8 1 7 ++
  [false, false, true] ++
  [true, false, false] ++ QCSD_natToUnary 14 ++ QCSD_natToUnary 13

def ovl2Bits : List Bool :=
  QCSD_natToUnary 3 ++ QCSD_natToUnary 22 ++
  [false, false, false] ++ QCSD_natToUnary 0 ++
  [false, false, false] ++ QCSD_natToUnary 1 ++
  [false, false, false] ++ QCSD_natToUnary 2 ++
  [false, true, false] ++ encodeXorAt 4 3 0 ++ encodeXorAt 9 8 1 ++ encodeEqAt 14 2 13 ++
  [false, false, true] ++
  [true, false, false] ++ QCSD_natToUnary 20 ++ QCSD_natToUnary 19

theorem encodeCircuit_ovl0 :
    QCSD_encodeCircuit (linearMapCheckCircuit 0 1 (fun _ _ => true)) = ovl0Bits := by
  rw [encodeCircuit_linearMapCheckCircuit]
  simp [ovl0Bits, encodeParityRow, parityRowStart, parityRowHits, parityEqWire, prefixHits,
    List.range_succ, List.append_assoc]

theorem encodeCircuit_ovl1 :
    QCSD_encodeCircuit (linearMapCheckCircuit 1 1 (fun _ _ => true)) = ovl1Bits := by
  rw [encodeCircuit_linearMapCheckCircuit]
  simp [ovl1Bits, encodeParityRow, parityRowStart, parityRowHits, parityEqWire, prefixHits,
    List.range_succ, List.append_assoc]

theorem encodeCircuit_ovl2 :
    QCSD_encodeCircuit (linearMapCheckCircuit 2 1 (fun _ _ => true)) = ovl2Bits := by
  rw [encodeCircuit_linearMapCheckCircuit]
  simp [ovl2Bits, encodeParityRow, parityRowStart, parityRowHits, parityEqWire, prefixHits,
    List.range_succ, List.append_assoc]

/-!
## Section 5: Exact & Polynomial Encoded Network Length Bounds
-/

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

/-- Sharp quadratic upper bound on `(QCSD_encodeCircuit c).length` for any well-formed circuit `c`. -/
theorem encodeCircuit_length_le_size (c : QCSD_BoolCircuit) (hwf : QCSD_circuitWF c) :
    (QCSD_encodeCircuit c).length ≤
      2 + 6 * QCSD_circuitSize c + 2 * (QCSD_circuitSize c) ^ 2 := by
  unfold QCSD_encodeCircuit
  simp only [List.length_append, natToUnary_length]
  have hflat : (c.gates.flatMap QCSD_encodeGate).length ≤
      c.gates.length * (5 + 2 * QCSD_circuitSize c) :=
    flatMap_length_le c.gates QCSD_encodeGate _ (encodeGate_length_le_of_wf c hwf)
  set sz := QCSD_circuitSize c
  have hdef : c.numInputs + c.gates.length = sz := rfl
  have hgl : c.gates.length ≤ sz := by omega
  have hmul : c.gates.length * (5 + 2 * sz) ≤ sz * (5 + 2 * sz) :=
    Nat.mul_le_mul_right _ hgl
  have hexp : sz * (5 + 2 * sz) = 5 * sz + 2 * sz ^ 2 := by ring
  omega

/-- **Explicit Structural Encoded Length Bound**: bounds `(QCSD_encodeNet2 (padNet padV N)).length`
explicitly in terms of `N.m`, `N.k`, `padV`, and `maxCircuitSize`. -/
theorem encodeNet2_padNet_length_le
    (padV maxCircuitSize : ℕ) (N : QCSD_BoolTensorNetwork2)
    (hmax : ∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ maxCircuitSize) :
    (QCSD_encodeNet2 (padNet padV N)).length ≤
      N.m + N.k + 2 + 7 * padV +
      N.k * (2 * N.m + 2) +
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2) := by
  have hcost : (QCSD_encodeNet2 (padNet padV N)).length = (QCSD_encodeNet2 N).length + 7 * padV :=
    padNet_netCost2_eq padV N
  rw [hcost]
  unfold QCSD_encodeNet2
  simp only [List.length_append, natToUnary_length]
  have hends :
      ((List.finRange N.k).flatMap (fun e =>
        QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val)).length ≤
      N.k * (2 * N.m + 2) := by
    have hb := flatMap_length_le (List.finRange N.k)
      (fun e => QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val)
      (2 * N.m + 2)
      (fun e _ => by
        simp only [List.length_append, natToUnary_length]
        have h1 := (N.ends e).1.isLt
        have h2 := (N.ends e).2.isLt
        omega)
    simpa [List.length_finRange] using hb
  have hpreds :
      ((List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v))).length ≤
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2) := by
    have hb := flatMap_length_le (List.finRange N.m)
      (fun v => QCSD_encodeCircuit (N.pred v))
      (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2)
      (fun v _ => by
        have hc := encodeCircuit_length_le_size (N.pred v) (N.wf v)
        have hv := hmax v
        have hsq : (QCSD_circuitSize (N.pred v)) ^ 2 ≤ maxCircuitSize ^ 2 :=
          Nat.pow_le_pow_left hv 2
        omega)
    simpa [List.length_finRange] using hb
  omega

/-- **Cubic `O(n^3)` Encoded Length Bound**: when `N.m ≤ Cm * n`, `N.k ≤ Ck * n`,
`maxCircuitSize ≤ Cs * n`, and `padV ≤ Cp * n ^ 3` (for `1 ≤ n`),
`(QCSD_encodeNet2 (padNet padV N)).length` is `O(n^3)` with explicit constant. -/
theorem encodeNet2_padNet_length_cubic
    {n Cm Ck Cs Cp padV maxCircuitSize : ℕ} (hn : 1 ≤ n)
    (N : QCSD_BoolTensorNetwork2)
    (hm : N.m ≤ Cm * n)
    (hk : N.k ≤ Ck * n)
    (hpad : padV ≤ Cp * n ^ 3)
    (hsz : maxCircuitSize ≤ Cs * n)
    (hmax : ∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ maxCircuitSize) :
    (QCSD_encodeNet2 (padNet padV N)).length ≤
      (2 + 3 * Cm + 3 * Ck + 7 * Cp + 2 * Ck * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ 3 := by
  have hbase := encodeNet2_padNet_length_le padV maxCircuitSize N hmax
  have hn13 : n ≤ n ^ 3 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 3 by decide)
  have hn23 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by decide)
  have h13 : 1 ≤ n ^ 3 := Nat.one_le_pow 3 n hn
  have hm3 : N.m ≤ Cm * n ^ 3 := hm.trans (Nat.mul_le_mul_left Cm hn13)
  have hk3 : N.k ≤ Ck * n ^ 3 := hk.trans (Nat.mul_le_mul_left Ck hn13)
  have hends3 : N.k * (2 * N.m + 2) ≤ (2 * Ck * Cm + 2 * Ck) * n ^ 3 := by
    calc
      N.k * (2 * N.m + 2) ≤ (Ck * n) * (2 * (Cm * n) + 2) :=
        Nat.mul_le_mul hk (by omega)
      _ = 2 * Ck * Cm * n ^ 2 + 2 * Ck * n := by ring
      _ ≤ 2 * Ck * Cm * n ^ 3 + 2 * Ck * n ^ 3 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hn23) (Nat.mul_le_mul_left _ hn13)
      _ = (2 * Ck * Cm + 2 * Ck) * n ^ 3 := by ring
  have hpreds3 :
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2) ≤
      (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ 3 := by
    have hsz2 : maxCircuitSize ^ 2 ≤ (Cs * n) ^ 2 := Nat.pow_le_pow_left hsz 2
    calc
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2)
          ≤ (Cm * n) * (2 + 6 * (Cs * n) + 2 * (Cs * n) ^ 2) :=
        Nat.mul_le_mul hm (by omega)
      _ = 2 * Cm * n + 6 * Cm * Cs * n ^ 2 + 2 * Cm * Cs ^ 2 * n ^ 3 := by ring
      _ ≤ 2 * Cm * n ^ 3 + 6 * Cm * Cs * n ^ 3 + 2 * Cm * Cs ^ 2 * n ^ 3 := by
        apply Nat.add_le_add
        · exact Nat.add_le_add (Nat.mul_le_mul_left _ hn13) (Nat.mul_le_mul_left _ hn23)
        · exact le_rfl
      _ = (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ 3 := by ring
  have hpad7 : 7 * padV ≤ 7 * Cp * n ^ 3 := by
    calc
      7 * padV ≤ 7 * (Cp * n ^ 3) := Nat.mul_le_mul_left 7 hpad
      _ = 7 * Cp * n ^ 3 := by ring
  have h2 : 2 ≤ 2 * n ^ 3 := by omega
  have hrhs :
      Cm * n ^ 3 + Ck * n ^ 3 + 2 * n ^ 3 + 7 * Cp * n ^ 3 +
        (2 * Ck * Cm + 2 * Ck) * n ^ 3 +
        (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ 3 =
      (2 + 3 * Cm + 3 * Ck + 7 * Cp + 2 * Ck * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ 3 := by
    ring
  omega

/-- **General Polynomial Encoded Length Bound (`O(n^(max dp (2 * ds + 1)))`)**: directly handles
quadratic `maxCircuitSize ≤ Cs * n ^ 2` (such as `rawPred_size_and_deg`'s `500 * S ^ 2` bound). -/
theorem encodeNet2_padNet_length_poly
    {n ds dp Cm Ck Cs Cp padV maxCircuitSize : ℕ} (hn : 1 ≤ n)
    (N : QCSD_BoolTensorNetwork2)
    (hm : N.m ≤ Cm * n)
    (hk : N.k ≤ Ck * n)
    (hpad : padV ≤ Cp * n ^ dp)
    (hsz : maxCircuitSize ≤ Cs * n ^ ds)
    (hmax : ∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ maxCircuitSize) :
    let D := max dp (max 2 (2 * ds + 1))
    (QCSD_encodeNet2 (padNet padV N)).length ≤
      (2 + 3 * Cm + 3 * Ck + 7 * Cp + 2 * Ck * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ D := by
  intro D
  have hbase := encodeNet2_padNet_length_le padV maxCircuitSize N hmax
  have hD_dp : dp ≤ D := le_max_left _ _
  have hD_2 : 2 ≤ D := (le_max_left 2 (2 * ds + 1)).trans (le_max_right dp _)
  have hD_2ds1 : 2 * ds + 1 ≤ D := (le_max_right 2 (2 * ds + 1)).trans (le_max_right dp _)
  have h1D : 1 ≤ n ^ D := Nat.one_le_pow D n hn
  have hn1D : n ≤ n ^ D := by
    simpa using Nat.pow_le_pow_right hn (show 1 ≤ D by omega)
  have hn2D : n ^ 2 ≤ n ^ D := Nat.pow_le_pow_right hn hD_2
  have hndpD : n ^ dp ≤ n ^ D := Nat.pow_le_pow_right hn hD_dp
  have hnds1D : n ^ (ds + 1) ≤ n ^ D := Nat.pow_le_pow_right hn (by omega)
  have hn2ds1D : n ^ (2 * ds + 1) ≤ n ^ D := Nat.pow_le_pow_right hn hD_2ds1
  have hmD : N.m ≤ Cm * n ^ D := hm.trans (Nat.mul_le_mul_left Cm hn1D)
  have hkD : N.k ≤ Ck * n ^ D := hk.trans (Nat.mul_le_mul_left Ck hn1D)
  have hpadD : 7 * padV ≤ 7 * Cp * n ^ D := by
    calc
      7 * padV ≤ 7 * (Cp * n ^ dp) := Nat.mul_le_mul_left 7 hpad
      _ = 7 * Cp * n ^ dp := by ring
      _ ≤ 7 * Cp * n ^ D := Nat.mul_le_mul_left _ hndpD
  have hendsD : N.k * (2 * N.m + 2) ≤ (2 * Ck * Cm + 2 * Ck) * n ^ D := by
    calc
      N.k * (2 * N.m + 2) ≤ (Ck * n) * (2 * (Cm * n) + 2) := Nat.mul_le_mul hk (by omega)
      _ = 2 * Ck * Cm * n ^ 2 + 2 * Ck * n := by ring
      _ ≤ 2 * Ck * Cm * n ^ D + 2 * Ck * n ^ D :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hn2D) (Nat.mul_le_mul_left _ hn1D)
      _ = (2 * Ck * Cm + 2 * Ck) * n ^ D := by ring
  have hpredsD :
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2) ≤
      (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ D := by
    have hsz2 : maxCircuitSize ^ 2 ≤ (Cs * n ^ ds) ^ 2 := Nat.pow_le_pow_left hsz 2
    have hexp_mid : (Cm * n) * (6 * (Cs * n ^ ds)) = 6 * Cm * Cs * n ^ (ds + 1) := by ring
    have hexp_hi : (Cm * n) * (2 * (Cs * n ^ ds) ^ 2) = 2 * Cm * Cs ^ 2 * n ^ (2 * ds + 1) := by
      ring
    calc
      N.m * (2 + 6 * maxCircuitSize + 2 * maxCircuitSize ^ 2)
          ≤ (Cm * n) * (2 + 6 * (Cs * n ^ ds) + 2 * (Cs * n ^ ds) ^ 2) :=
        Nat.mul_le_mul hm (by omega)
      _ = 2 * Cm * n + (Cm * n) * (6 * (Cs * n ^ ds)) + (Cm * n) * (2 * (Cs * n ^ ds) ^ 2) := by
        ring
      _ = 2 * Cm * n + 6 * Cm * Cs * n ^ (ds + 1) + 2 * Cm * Cs ^ 2 * n ^ (2 * ds + 1) := by
        rw [hexp_mid, hexp_hi]
      _ ≤ 2 * Cm * n ^ D + 6 * Cm * Cs * n ^ D + 2 * Cm * Cs ^ 2 * n ^ D := by
        apply Nat.add_le_add
        · exact Nat.add_le_add (Nat.mul_le_mul_left _ hn1D) (Nat.mul_le_mul_left _ hnds1D)
        · exact Nat.mul_le_mul_left _ hn2ds1D
      _ = (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ D := by ring
  have h2 : 2 ≤ 2 * n ^ D := by omega
  have hrhs :
      Cm * n ^ D + Ck * n ^ D + 2 * n ^ D + 7 * Cp * n ^ D +
        (2 * Ck * Cm + 2 * Ck) * n ^ D +
        (2 * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ D =
      (2 + 3 * Cm + 3 * Ck + 7 * Cp + 2 * Ck * Cm + 6 * Cm * Cs + 2 * Cm * Cs ^ 2) * n ^ D := by
    ring
  omega

end Branch7EncodeSpec
