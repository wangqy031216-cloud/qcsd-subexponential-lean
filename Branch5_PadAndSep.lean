import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.InformationTheory.Hamming
import Mathlib.Computability.Encoding
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import QCSD.Defs

namespace Branch5PadAndSep

open QCSD.Defs

/-!
## Part 1: Isolated Constant-True Vertex Padding Functor `padNet`
-/

/-- Zero-input constant-`true` circuit (`numInputs = 0`, single `QCSD_GateOp.tt` gate). -/
def constTrueZeroIn : QCSD_BoolCircuit :=
  ⟨0, [⟨QCSD_GateOp.tt, 0, 0⟩]⟩

lemma constTrueZeroIn_numInputs : constTrueZeroIn.numInputs = 0 := rfl

lemma constTrueZeroIn_gates_length : constTrueZeroIn.gates.length = 1 := rfl

lemma constTrueZeroIn_size : QCSD_circuitSize constTrueZeroIn = 1 := rfl

lemma constTrueZeroIn_wf : QCSD_circuitWF constTrueZeroIn := by
  intro i g hopt
  unfold QCSD_gateAtOpt constTrueZeroIn at hopt
  by_cases hi : i < ([⟨QCSD_GateOp.tt, 0, 0⟩] : List QCSD_Gate).length
  · rw [dite_eq_left hi] at hopt
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    cases hopt
    trivial
  · rw [dite_eq_right hi] at hopt
    cases hopt

lemma constTrueZeroIn_eval (inp : ℕ → Bool) :
    QCSD_evalCircuit constTrueZeroIn inp = true := rfl

lemma constTrueZeroIn_encode :
    QCSD_encodeCircuit constTrueZeroIn = [false, true, false, false, false, true] := rfl

lemma constTrueZeroIn_encode_length :
    (QCSD_encodeCircuit constTrueZeroIn).length = 6 := rfl

/-- Shifted endpoint map embedding `Fin N.m` into the first `N.m` vertices of `Fin (N.m + padV)`. -/
def padEnds (padV : ℕ) (N : QCSD_BoolTensorNetwork2) (e : Fin N.k) :
    Fin (N.m + padV) × Fin (N.m + padV) :=
  (⟨(N.ends e).1.val, Nat.lt_of_lt_of_le (N.ends e).1.isLt (Nat.le_add_right N.m padV)⟩,
   ⟨(N.ends e).2.val, Nat.lt_of_lt_of_le (N.ends e).2.isLt (Nat.le_add_right N.m padV)⟩)

lemma padEnds_noLoop (padV : ℕ) (N : QCSD_BoolTensorNetwork2) (e : Fin N.k) :
    (padEnds padV N e).1 ≠ (padEnds padV N e).2 := by
  intro heq
  have hval : (N.ends e).1.val = (N.ends e).2.val :=
    congrArg (fun u : Fin (N.m + padV) => u.val) heq
  exact N.noLoop e (Fin.ext hval)

lemma padEnds_incidentList_lt (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (N.m + padV)) (h : v.val < N.m) :
    QCSD_incidentList (N.m + padV) N.k (padEnds padV N) v =
      QCSD_incidentList N.m N.k N.ends ⟨v.val, h⟩ := by
  unfold QCSD_incidentList
  have hs :
      Finset.univ.filter (fun e : Fin N.k => (padEnds padV N e).1 = v ∨ (padEnds padV N e).2 = v) =
      Finset.univ.filter (fun e : Fin N.k =>
        (N.ends e).1 = ⟨v.val, h⟩ ∨ (N.ends e).2 = ⟨v.val, h⟩) := by
    ext e
    simp [padEnds, Fin.ext_iff]
  rw [hs]

lemma padEnds_incidentList_ge (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (N.m + padV)) (h : N.m ≤ v.val) :
    QCSD_incidentList (N.m + padV) N.k (padEnds padV N) v = [] := by
  unfold QCSD_incidentList
  have hemp : Finset.univ.filter
      (fun e : Fin N.k => (padEnds padV N e).1 = v ∨ (padEnds padV N e).2 = v) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e _
    simp only [padEnds, Fin.ext_iff, not_or]
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le (N.ends e).1.isLt h),
           Nat.ne_of_lt (Nat.lt_of_lt_of_le (N.ends e).2.isLt h)⟩
  rw [hemp]
  exact Finset.sort_empty (· ≤ ·)

/-- Vertex predicate map for `padNet`: original circuit on `< N.m`, `constTrueZeroIn` on `≥ N.m`. -/
def padPred (padV : ℕ) (N : QCSD_BoolTensorNetwork2) (v : Fin (N.m + padV)) :
    QCSD_BoolCircuit :=
  if h : v.val < N.m then N.pred ⟨v.val, h⟩ else constTrueZeroIn

/-- Isolated constant-true vertex padding functor adding `padV` degree-0 `true` vertices. -/
def padNet (padV : ℕ) (N : QCSD_BoolTensorNetwork2) : QCSD_BoolTensorNetwork2 :=
  { m := N.m + padV
    k := N.k
    ends := padEnds padV N
    noLoop := padEnds_noLoop padV N
    pred := padPred padV N
    arity := fun v => by
      unfold padPred
      by_cases h : v.val < N.m
      · rw [dite_eq_left h, padEnds_incidentList_lt padV N v h]
        exact N.arity ⟨v.val, h⟩
      · rw [dite_eq_right h, padEnds_incidentList_ge padV N v (Nat.le_of_not_lt h)]
        rfl
    wf := fun v => by
      unfold padPred
      by_cases h : v.val < N.m
      · rw [dite_eq_left h]
        exact N.wf ⟨v.val, h⟩
      · rw [dite_eq_right h]
        exact constTrueZeroIn_wf }

@[simp] theorem padNet_m (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    (padNet padV N).m = N.m + padV := rfl

@[simp] theorem padNet_k (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    (padNet padV N).k = N.k := rfl

@[simp] theorem padNet_edgeCount2 (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_edgeCount2 (padNet padV N) = QCSD_edgeCount2 N := rfl

theorem padNet_pred_lt (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : v.val < N.m) :
    (padNet padV N).pred v = N.pred ⟨v.val, h⟩ := by
  change padPred padV N v = N.pred ⟨v.val, h⟩
  exact dite_eq_left h

theorem padNet_pred_ge (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : N.m ≤ v.val) :
    (padNet padV N).pred v = constTrueZeroIn := by
  change padPred padV N v = constTrueZeroIn
  exact dite_eq_right (Nat.not_lt.mpr h)

theorem padNet_incidentList_lt (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : v.val < N.m) :
    QCSD_incidentList (padNet padV N).m (padNet padV N).k (padNet padV N).ends v =
      QCSD_incidentList N.m N.k N.ends ⟨v.val, h⟩ :=
  padEnds_incidentList_lt padV N v h

theorem padNet_incidentList_lt_val (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : v.val < N.m) :
    (QCSD_incidentList (padNet padV N).m (padNet padV N).k (padNet padV N).ends v).map Fin.val =
      (QCSD_incidentList N.m N.k N.ends ⟨v.val, h⟩).map Fin.val :=
  congrArg (List.map Fin.val) (padNet_incidentList_lt padV N v h)

theorem padNet_incidentList_ge (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : N.m ≤ v.val) :
    QCSD_incidentList (padNet padV N).m (padNet padV N).k (padNet padV N).ends v = [] :=
  padEnds_incidentList_ge padV N v h

theorem padNet_deg2_lt (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : v.val < N.m) :
    QCSD_deg2 (padNet padV N) v = QCSD_deg2 N ⟨v.val, h⟩ := by
  unfold QCSD_deg2
  rw [padNet_incidentList_lt padV N v h]
  rfl

theorem padNet_deg2_ge (padV : ℕ) (N : QCSD_BoolTensorNetwork2)
    (v : Fin (padNet padV N).m) (h : N.m ≤ v.val) :
    QCSD_deg2 (padNet padV N) v = 0 := by
  unfold QCSD_deg2
  rw [padNet_incidentList_ge padV N v h]
  rfl

/-- Contraction invariance under `padNet`. -/
theorem padNet_contraction2 (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_contraction2 (padNet padV N) = QCSD_contraction2 N := by
  unfold QCSD_contraction2
  refine Finset.sum_congr rfl (fun x _ => ?_)
  change (Finset.univ.prod (fun v : Fin (N.m + padV) => _)) = _
  rw [Fin.prod_univ_add]
  have hright :
      Finset.univ.prod (fun u : Fin padV =>
        if QCSD_evalCircuit ((padNet padV N).pred (Fin.natAdd N.m u))
            (fun i => if h : i < (QCSD_incidentList (padNet padV N).m (padNet padV N).k
                (padNet padV N).ends (Fin.natAdd N.m u)).length
              then x ((QCSD_incidentList (padNet padV N).m (padNet padV N).k
                (padNet padV N).ends (Fin.natAdd N.m u)).get ⟨i, h⟩)
              else false) then 1 else 0) = 1 := by
    apply Finset.prod_eq_one
    intro u _
    have hge : N.m ≤ (Fin.natAdd N.m u).val := by simp
    rw [padNet_pred_ge padV N (Fin.natAdd N.m u) hge, constTrueZeroIn_eval]
    rfl
  rw [hright, mul_one]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  have hlt : (Fin.castAdd padV v).val < N.m := v.isLt
  have hv_eq : (⟨(Fin.castAdd padV v).val, hlt⟩ : Fin N.m) = v := by ext; rfl
  have hpred : (padNet padV N).pred (Fin.castAdd padV v) = N.pred v := by
    rw [padNet_pred_lt padV N (Fin.castAdd padV v) hlt, hv_eq]
  have hinc : QCSD_incidentList (padNet padV N).m (padNet padV N).k
      (padNet padV N).ends (Fin.castAdd padV v) =
      QCSD_incidentList N.m N.k N.ends v := by
    rw [padNet_incidentList_lt padV N (Fin.castAdd padV v) hlt, hv_eq]
  rw [hpred, hinc]
  rfl

/-- Maximum degree invariance under `padNet`. -/
theorem padNet_maxDeg2 (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_maxDeg2 (padNet padV N) = QCSD_maxDeg2 N := by
  unfold QCSD_maxDeg2
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    by_cases h : v.val < N.m
    · rw [padNet_deg2_lt padV N v h]
      let u0 : Fin N.m := ⟨v.val, h⟩
      exact Finset.le_sup (f := fun u : Fin N.m => QCSD_deg2 N u) (Finset.mem_univ u0)
    · rw [padNet_deg2_ge padV N v (Nat.le_of_not_lt h)]
      exact Nat.zero_le _
  · apply Finset.sup_le
    intro v _
    let v' : Fin (padNet padV N).m :=
      ⟨v.val, Nat.lt_of_lt_of_le v.isLt (Nat.le_add_right N.m padV)⟩
    have hv_eq : (⟨v'.val, v.isLt⟩ : Fin N.m) = v := by ext; rfl
    have hdeg : QCSD_deg2 N v = QCSD_deg2 (padNet padV N) v' := by
      rw [padNet_deg2_lt padV N v' v.isLt, hv_eq]
    rw [hdeg]
    exact Finset.le_sup (f := fun u : Fin (padNet padV N).m => QCSD_deg2 (padNet padV N) u)
      (Finset.mem_univ v')

/-!
### Encoding Decomposition, `QCSD_netCost2` Bound, Prefix `true` Run, and `QCSD_TCClass2`
-/

lemma finRange_add_split (a b : ℕ) :
    List.finRange (a + b) =
      (List.finRange a).map (Fin.castAdd b) ++ (List.finRange b).map (Fin.natAdd a) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    apply Fin.ext
    by_cases hi : i < a
    · have hi' : i < ((List.finRange a).map (Fin.castAdd b)).length := by simpa using hi
      rw [List.getElem_append_left hi']
      simp
    · have hge : ((List.finRange a).map (Fin.castAdd b)).length ≤ i := by
        simp; omega
      rw [List.getElem_append_right hge]
      simp; omega

lemma flatMap_const_length {α β : Type*} :
    ∀ (l : List α) (c : List β),
      (l.flatMap (fun _ => c)).length = l.length * c.length
  | [], _ => by simp
  | _ :: xs, c => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      flatMap_const_length xs c]
    ring

/-- Exact bit-list decomposition of `QCSD_encodeNet2 (padNet padV N)` in terms of `QCSD_encodeNet2 N`. -/
theorem encodeNet2_padNet_decomp (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_encodeNet2 (padNet padV N) =
      List.replicate padV true ++
      QCSD_encodeNet2 N ++
      (List.finRange padV).flatMap (fun _ => QCSD_encodeCircuit constTrueZeroIn) := by
  unfold QCSD_encodeNet2
  dsimp only [padNet]
  have hunary :
      QCSD_natToUnary (N.m + padV) =
        List.replicate padV true ++ QCSD_natToUnary N.m := by
    unfold QCSD_natToUnary
    rw [Nat.add_comm N.m padV, List.replicate_add, List.append_assoc]
  have hpreds :
      (List.finRange (N.m + padV)).flatMap (fun v =>
        QCSD_encodeCircuit (padPred padV N v)) =
      (List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v)) ++
      (List.finRange padV).flatMap (fun _ => QCSD_encodeCircuit constTrueZeroIn) := by
    rw [finRange_add_split N.m padV, List.flatMap_append, List.flatMap_map, List.flatMap_map]
    congr 1
    · refine List.flatMap_congr (fun v _ => ?_)
      have hlt : (Fin.castAdd padV v).val < N.m := v.isLt
      have hv_eq : (⟨(Fin.castAdd padV v).val, hlt⟩ : Fin N.m) = v := by ext; rfl
      unfold padPred
      rw [dite_eq_left hlt, hv_eq]
    · refine List.flatMap_congr (fun u _ => ?_)
      have hnot : ¬ ((Fin.natAdd N.m u).val < N.m) := by simp
      unfold padPred
      rw [dite_eq_right hnot]
  rw [hunary, hpreds]
  simp only [padEnds, List.append_assoc]

/-- Exact linear identity for `QCSD_netCost2 (padNet padV N)`: each padded vertex adds `1 + 6 = 7` bits. -/
theorem padNet_netCost2_eq (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_netCost2 (padNet padV N) = QCSD_netCost2 N + 7 * padV := by
  unfold QCSD_netCost2
  rw [encodeNet2_padNet_decomp]
  simp only [List.length_append, List.length_replicate, flatMap_const_length,
    List.length_finRange, constTrueZeroIn_encode_length]
  omega

/-- Linear upper bound on `QCSD_netCost2 (padNet padV N)`. -/
theorem padNet_netCost2_le (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    QCSD_netCost2 (padNet padV N) ≤ QCSD_netCost2 N + 7 * padV :=
  Nat.le_of_eq (padNet_netCost2_eq padV N)

/-- Every `QCSD_encodeNet2 M` begins with `M.m` `true` bits followed immediately by a `false` delimiter. -/
theorem encodeNet2_prefix_true (M : QCSD_BoolTensorNetwork2) :
    (QCSD_encodeNet2 M).take M.m = List.replicate M.m true ∧
    M.m < (QCSD_encodeNet2 M).length ∧
    (QCSD_encodeNet2 M).getD M.m true = false := by
  unfold QCSD_encodeNet2
  set rest := QCSD_natToUnary M.k ++
    (List.finRange M.k).flatMap (fun e =>
      QCSD_natToUnary (M.ends e).1.val ++ QCSD_natToUnary (M.ends e).2.val) ++
    (List.finRange M.m).flatMap (fun v => QCSD_encodeCircuit (M.pred v))
  have hshape :
      QCSD_natToUnary M.m ++ QCSD_natToUnary M.k ++
        (List.finRange M.k).flatMap (fun e =>
          QCSD_natToUnary (M.ends e).1.val ++ QCSD_natToUnary (M.ends e).2.val) ++
        (List.finRange M.m).flatMap (fun v => QCSD_encodeCircuit (M.pred v)) =
      List.replicate M.m true ++ (false :: rest) := by
    simp [QCSD_natToUnary, rest, List.append_assoc]
  rw [hshape]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · have hge : (List.replicate M.m true).length ≤ M.m := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    simp

/-- `QCSD_encodeNet2 (padNet padV N)` starts with `N.m + padV` `true` bits and has length `> N.m + padV`. -/
theorem encodeNet2_padNet_prefix_true (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    (QCSD_encodeNet2 (padNet padV N)).take (N.m + padV) = List.replicate (N.m + padV) true ∧
    N.m + padV < (QCSD_encodeNet2 (padNet padV N)).length := by
  have h := encodeNet2_prefix_true (padNet padV N)
  exact ⟨h.1, h.2.1⟩

theorem encodeNet2_padNet_getD_sep (padV : ℕ) (N : QCSD_BoolTensorNetwork2) :
    (QCSD_encodeNet2 (padNet padV N)).getD (N.m + padV) true = false :=
  (encodeNet2_prefix_true (padNet padV N)).2.2

/-- Preservation of `QCSD_TCAdmissible` for the updated polynomial constants of `padNet`. -/
theorem padNet_TCAdmissible
    {CΔ : ℝ} {km Km kcost Kcost kpred Kpred C d : ℕ}
    (hadm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred) :
    QCSD_TCAdmissible CΔ (max km d) (Km + C) (max kcost d) (Kcost + 7 * C) kpred (max Kpred 1) := by
  rcases hadm with ⟨hCΔ, hKm, hKcost, hKpred⟩
  exact ⟨hCΔ, by omega, by omega, le_max_of_le_left hKpred⟩

/-- Preservation of `QCSD_TCClass2` under `padNet` when `padV ≤ C * (QCSD_edgeCount2 N) ^ d`. -/
theorem padNet_mem_TCClass2
    {CΔ : ℝ} {km Km kcost Kcost kpred Kpred C d : ℕ}
    {N : QCSD_BoolTensorNetwork2} {padV : ℕ}
    (hTC : QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred N)
    (hpad : padV ≤ C * (QCSD_edgeCount2 N) ^ d) :
    QCSD_TCClass2 CΔ (max km d) (Km + C) (max kcost d) (Kcost + 7 * C) kpred (max Kpred 1)
      (padNet padV N) := by
  rcases hTC with ⟨hk2, hdeg, hm, hcost, hpred⟩
  set S := QCSD_edgeCount2 N
  have hS1 : 1 ≤ S := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hk2
  · rw [padNet_maxDeg2, padNet_edgeCount2]
    exact hdeg
  · rw [padNet_m, padNet_edgeCount2]
    have hpow1 : S ^ km ≤ S ^ max km d := Nat.pow_le_pow_right hS1 (le_max_left km d)
    have hpow2 : S ^ d ≤ S ^ max km d := Nat.pow_le_pow_right hS1 (le_max_right km d)
    calc
      N.m + padV ≤ Km * S ^ km + C * S ^ d := Nat.add_le_add hm hpad
      _ ≤ Km * S ^ max km d + C * S ^ max km d :=
        Nat.add_le_add (Nat.mul_le_mul_left Km hpow1) (Nat.mul_le_mul_left C hpow2)
      _ = (Km + C) * S ^ max km d := by ring
  · rw [padNet_netCost2_eq, padNet_edgeCount2]
    have hpow1 : S ^ kcost ≤ S ^ max kcost d := Nat.pow_le_pow_right hS1 (le_max_left kcost d)
    have hpow2 : S ^ d ≤ S ^ max kcost d := Nat.pow_le_pow_right hS1 (le_max_right kcost d)
    have hpad7 : 7 * padV ≤ (7 * C) * S ^ d := by
      calc
        7 * padV ≤ 7 * (C * S ^ d) := Nat.mul_le_mul_left 7 hpad
        _ = (7 * C) * S ^ d := by ring
    calc
      QCSD_netCost2 N + 7 * padV ≤ Kcost * S ^ kcost + (7 * C) * S ^ d :=
        Nat.add_le_add hcost hpad7
      _ ≤ Kcost * S ^ max kcost d + (7 * C) * S ^ max kcost d :=
        Nat.add_le_add (Nat.mul_le_mul_left Kcost hpow1) (Nat.mul_le_mul_left (7 * C) hpow2)
      _ = (Kcost + 7 * C) * S ^ max kcost d := by ring
  · intro v
    rw [padNet_edgeCount2]
    by_cases hv : v.val < N.m
    · rw [padNet_pred_lt padV N v hv]
      calc
        QCSD_circuitSize (N.pred ⟨v.val, hv⟩) ≤ Kpred * S ^ kpred := hpred ⟨v.val, hv⟩
        _ ≤ max Kpred 1 * S ^ kpred := Nat.mul_le_mul_right _ (le_max_left Kpred 1)
    · rw [padNet_pred_ge padV N v (Nat.le_of_not_lt hv), constTrueZeroIn_size]
      have hS_pow : 1 ≤ S ^ kpred := Nat.one_le_pow kpred S hS1
      have hK_one : 1 ≤ max Kpred 1 := le_max_right Kpred 1
      calc
        1 = 1 * 1 := rfl
        _ ≤ max Kpred 1 * S ^ kpred := Nat.mul_le_mul hK_one hS_pow

/-- Parametric corollary of `padNet_mem_TCClass2` when `padV ≤ C * n ^ d` and `n ≤ QCSD_edgeCount2 N`. -/
theorem padNet_mem_TCClass2_of_le
    {CΔ : ℝ} {km Km kcost Kcost kpred Kpred C d n : ℕ}
    {N : QCSD_BoolTensorNetwork2} {padV : ℕ}
    (hTC : QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred N)
    (hn : n ≤ QCSD_edgeCount2 N)
    (hpad : padV ≤ C * n ^ d) :
    QCSD_TCClass2 CΔ (max km d) (Km + C) (max kcost d) (Kcost + 7 * C) kpred (max Kpred 1)
      (padNet padV N) := by
  apply padNet_mem_TCClass2 hTC
  exact hpad.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hn d))

/-!
## Part 2: All Three Variants (`Exact`, `Sep`, `Le`) Combinatorial, Prefix, Witness & Encoding Laws
-/

/-! ### 2A. Witness Bit Encoding / Decoding Bijection & Instance Encoding Lengths -/

@[simp] theorem natToUnary_length (m : ℕ) :
    (QCSD_natToUnary m).length = m + 1 := by
  simp [QCSD_natToUnary]

@[simp] theorem vecToBits_length {n : ℕ} (v : Fin n → ZMod 2) :
    (QCSD_vecToBits v).length = n := by
  simp [QCSD_vecToBits]

lemma vecToBits_eq_ofFn {n : ℕ} (v : Fin n → ZMod 2) :
    QCSD_vecToBits v = List.ofFn (fun i : Fin n => decide (v i = (1 : ZMod 2))) := by
  unfold QCSD_vecToBits
  exact (List.ofFn_eq_map).symm

/-- Exact bit length of `QCSD_encodeInstance inp` (`Exact` and `Le` input encoding). -/
theorem QCSD_encodeInstance_length (inp : QCSD_Instance) :
    (QCSD_encodeInstance inp).length = 3 * inp.n + inp.t + 2 := by
  unfold QCSD_encodeInstance
  simp only [List.length_append, natToUnary_length, vecToBits_length]
  omega

/-- Linear upper bound on `(QCSD_encodeInstance inp).length` when `inp.t ≤ 2 * inp.n`. -/
theorem QCSD_encodeInstance_length_le (inp : QCSD_Instance) (ht : inp.t ≤ 2 * inp.n) :
    (QCSD_encodeInstance inp).length ≤ 5 * inp.n + 2 := by
  rw [QCSD_encodeInstance_length]
  omega

/-- Homogeneous linear bound `(QCSD_encodeInstance inp).length ≤ 7 * inp.n` for `1 ≤ inp.n`, `t ≤ 2 * n`. -/
theorem QCSD_encodeInstance_length_le_mul (inp : QCSD_Instance)
    (hn : 1 ≤ inp.n) (ht : inp.t ≤ 2 * inp.n) :
    (QCSD_encodeInstance inp).length ≤ 7 * inp.n := by
  have h := QCSD_encodeInstance_length_le inp ht
  omega

/-- Exact bit length of `QCSD_encodeInstanceSep inp` (`Sep` input encoding). -/
theorem QCSD_encodeInstanceSep_length (inp : QCSD_InstanceSep) :
    (QCSD_encodeInstanceSep inp).length = 3 * inp.n + inp.t₀ + inp.t₁ + 3 := by
  unfold QCSD_encodeInstanceSep
  simp only [List.length_append, natToUnary_length, vecToBits_length]
  omega

/-- Linear upper bound on `(QCSD_encodeInstanceSep inp).length` when `t₀ ≤ n` and `t₁ ≤ n`. -/
theorem QCSD_encodeInstanceSep_length_le (inp : QCSD_InstanceSep)
    (ht₀ : inp.t₀ ≤ inp.n) (ht₁ : inp.t₁ ≤ inp.n) :
    (QCSD_encodeInstanceSep inp).length ≤ 5 * inp.n + 3 := by
  rw [QCSD_encodeInstanceSep_length]
  omega

/-- Homogeneous linear bound `(QCSD_encodeInstanceSep inp).length ≤ 8 * inp.n` for `1 ≤ inp.n`, `t₀, t₁ ≤ n`. -/
theorem QCSD_encodeInstanceSep_length_le_mul (inp : QCSD_InstanceSep)
    (hn : 1 ≤ inp.n) (ht₀ : inp.t₀ ≤ inp.n) (ht₁ : inp.t₁ ≤ inp.n) :
    (QCSD_encodeInstanceSep inp).length ≤ 8 * inp.n := by
  have h := QCSD_encodeInstanceSep_length_le inp ht₀ ht₁
  omega

/-- Canonical `2 * n`-bit witness encoding of a solution pair `(e₀, e₁)`. -/
def QCSD_encodeSolPair {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) : List Bool :=
  QCSD_vecToBits e₀ ++ QCSD_vecToBits e₁

lemma encodeSolPair_eq_ofFn {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) :
    QCSD_encodeSolPair e₀ e₁ =
      List.ofFn (fun i : Fin n => decide (e₀ i = 1)) ++
      List.ofFn (fun i : Fin n => decide (e₁ i = 1)) := by
  simp [QCSD_encodeSolPair, vecToBits_eq_ofFn]

@[simp] theorem encodeSolPair_length {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) :
    (QCSD_encodeSolPair e₀ e₁).length = 2 * n := by
  simp [QCSD_encodeSolPair, Nat.two_mul]

lemma zmod2_ite_decide_eq_one (x : ZMod 2) :
    (if decide (x = (1 : ZMod 2)) then (1 : ZMod 2) else 0) = x := by
  fin_cases x <;> rfl

lemma decide_ite_zmod2_eq_one (b : Bool) :
    decide ((if b then (1 : ZMod 2) else 0) = (1 : ZMod 2)) = b := by
  cases b <;> decide

lemma encodeSolPair_getElem_left {n : ℕ} (e₀ e₁ : Fin n → ZMod 2)
    (i : ℕ) (hi : i < n) :
    (QCSD_encodeSolPair e₀ e₁)[i]'(by simp [Nat.two_mul]; omega) =
      decide (e₀ ⟨i, hi⟩ = 1) := by
  have hi' : i < (QCSD_vecToBits e₀).length := by simpa using hi
  unfold QCSD_encodeSolPair
  rw [List.getElem_append_left hi']
  simp [QCSD_vecToBits]

lemma encodeSolPair_getElem_right {n : ℕ} (e₀ e₁ : Fin n → ZMod 2)
    (i : ℕ) (hi : i < n) :
    (QCSD_encodeSolPair e₀ e₁)[n + i]'(by simp [Nat.two_mul]; omega) =
      decide (e₁ ⟨i, hi⟩ = 1) := by
  have hge : (QCSD_vecToBits e₀).length ≤ n + i := by simp
  unfold QCSD_encodeSolPair
  rw [List.getElem_append_right hge]
  simp [QCSD_vecToBits]

/-- Left-inverse law: `QCSD_decodeSolPair` recovers `(e₀, e₁)` from `QCSD_encodeSolPair e₀ e₁`. -/
theorem decodeSolPair_encodeSolPair {n : ℕ} (e₀ e₁ : Fin n → ZMod 2) :
    QCSD_decodeSolPair n (QCSD_encodeSolPair e₀ e₁) = some (e₀, e₁) := by
  unfold QCSD_decodeSolPair
  rw [ite_eq_left (encodeSolPair_length e₀ e₁)]
  congr 1
  apply Prod.ext
  · dsimp only
    funext i
    have hlt : i.val < (QCSD_encodeSolPair e₀ e₁).length := by simp [Nat.two_mul]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
        encodeSolPair_getElem_left e₀ e₁ i.val i.isLt]
    exact zmod2_ite_decide_eq_one (e₀ i)
  · dsimp only
    funext i
    have hlt : n + i.val < (QCSD_encodeSolPair e₀ e₁).length := by simp [Nat.two_mul]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
        encodeSolPair_getElem_right e₀ e₁ i.val i.isLt]
    exact zmod2_ite_decide_eq_one (e₁ i)

/-- Exact bijection between `2 * n`-bit lists `w` and solution pairs `(e₀, e₁)` under `QCSD_decodeSolPair`. -/
theorem decodeSolPair_eq_some_iff {n : ℕ} {w : List Bool} {e₀ e₁ : Fin n → ZMod 2} :
    QCSD_decodeSolPair n w = some (e₀, e₁) ↔
      w.length = 2 * n ∧ QCSD_encodeSolPair e₀ e₁ = w := by
  constructor
  · intro hdec
    unfold QCSD_decodeSolPair at hdec
    by_cases hlen : w.length = 2 * n
    · rw [ite_eq_left hlen] at hdec
      injection hdec with hp
      have he₀ := (Prod.mk.inj hp).1
      have he₁ := (Prod.mk.inj hp).2
      subst he₀; subst he₁
      refine ⟨hlen, ?_⟩
      apply List.ext_getElem (by rw [encodeSolPair_length, hlen])
      intro j hj1 hj2
      by_cases hjn : j < n
      · rw [encodeSolPair_getElem_left _ _ j hjn]
        dsimp only
        rw [decide_ite_zmod2_eq_one, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hj2, Option.getD_some]
      · have hj_sub : j - n < n := by omega
        have hj_eq : n + (j - n) = j := by omega
        have h1 := encodeSolPair_getElem_right
          (fun i : Fin n => if w.getD i.val false then (1 : ZMod 2) else 0)
          (fun i : Fin n => if w.getD (n + i.val) false then (1 : ZMod 2) else 0)
          (j - n) hj_sub
        dsimp only at h1
        rw [decide_ite_zmod2_eq_one] at h1
        have hget : (QCSD_encodeSolPair
            (fun i : Fin n => if w.getD i.val false then (1 : ZMod 2) else 0)
            (fun i : Fin n => if w.getD (n + i.val) false then (1 : ZMod 2) else 0))[j]'hj1 =
            w.getD (n + (j - n)) false := by
          simpa [hj_eq] using h1
        rw [hget, hj_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
    · rw [ite_eq_right hlen] at hdec
      cases hdec
  · rintro ⟨_, rfl⟩
    exact decodeSolPair_encodeSolPair e₀ e₁

/-- Coordinatewise characterization of `(QCSD_encodeSolPair e₀ e₁).take pre.length = pre`. -/
theorem encodeSolPair_take_eq_iff {n : ℕ} (e₀ e₁ : Fin n → ZMod 2)
    (pre : List Bool) (hp : pre.length ≤ 2 * n) :
    (QCSD_encodeSolPair e₀ e₁).take pre.length = pre ↔
      (∀ (i : Fin n) (hi : i.val < pre.length), decide (e₀ i = 1) = pre[i.val]) ∧
      (∀ (i : Fin n) (hi : n + i.val < pre.length), decide (e₁ i = 1) = pre[n + i.val]) := by
  constructor
  · intro htake
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hget := congrArg (fun l : List Bool => l[i.val]?) htake
      have hlt : i.val < (QCSD_encodeSolPair e₀ e₁).length := by simp [Nat.two_mul]; omega
      rw [List.getElem?_take_of_lt hi, List.getElem?_eq_getElem hlt,
          List.getElem?_eq_getElem hi, Option.some.injEq,
          encodeSolPair_getElem_left e₀ e₁ i.val i.isLt] at hget
      exact hget
    · have hget := congrArg (fun l : List Bool => l[n + i.val]?) htake
      have hlt : n + i.val < (QCSD_encodeSolPair e₀ e₁).length := by simp [Nat.two_mul]
      rw [List.getElem?_take_of_lt hi, List.getElem?_eq_getElem hlt,
          List.getElem?_eq_getElem hi, Option.some.injEq,
          encodeSolPair_getElem_right e₀ e₁ i.val i.isLt] at hget
      exact hget
  · rintro ⟨h0, h1⟩
    apply List.ext_getElem
    · simp [Nat.min_eq_left hp]
    · intro j hj1 hj2
      rw [List.getElem_take]
      by_cases hjn : j < n
      · rw [encodeSolPair_getElem_left e₀ e₁ j hjn]
        exact h0 ⟨j, hjn⟩ hj2
      · have hj_sub : j - n < n := by omega
        have hj_eq : n + (j - n) = j := by omega
        have hright := encodeSolPair_getElem_right e₀ e₁ (j - n) hj_sub
        have hval := h1 ⟨j - n, hj_sub⟩ (by simp; omega)
        simpa [hj_eq] using hright.trans hval

/-! ### 2B. Linear Syndrome Uniqueness & Exact Solution Count Upper Bounds (`< 2 ^ (2 * n)`) -/

/-- Any subset of pairs `(e₀, e₁)` satisfying `e₀ + cycMul h e₁ = s` has cardinality `≤ 2 ^ n`. -/
lemma card_syndrome_sols_le_two_pow_n
    (n : ℕ) (h s : Fin n → ZMod 2)
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hLin : ∀ p ∈ sols, ∀ k : Fin n, p.1 k + QCSD_cycMul n h p.2 k = s k) :
    sols.card ≤ 2 ^ n := by
  have hinj : Set.InjOn Prod.snd (sols : Set ((Fin n → ZMod 2) × (Fin n → ZMod 2))) := by
    intro p hp q hq hsnd
    have hp' := hLin p hp
    have hq' := hLin q hq
    ext k
    · have hk1 := hp' k
      have hk2 := hq' k
      rw [hsnd] at hk1
      exact add_right_cancel (hk1.trans hk2.symm)
    · exact congrFun hsnd k
  have hle : sols.card ≤ (Finset.univ : Finset (Fin n → ZMod 2)).card :=
    Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) hinj
  have hcard : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
    simp [ZMod.card]
  omega

lemma card_syndrome_sols_lt_two_pow_two_mul
    (n : ℕ) (hn : 1 ≤ n) (h s : Fin n → ZMod 2)
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hLin : ∀ p ∈ sols, ∀ k : Fin n, p.1 k + QCSD_cycMul n h p.2 k = s k) :
    sols.card < 2 ^ (2 * n) := by
  have hle := card_syndrome_sols_le_two_pow_n n h s sols hLin
  have hpow : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem QCSD_count_le_two_pow_n (inp : QCSD_Instance) :
    QCSD_count inp ≤ 2 ^ inp.n := by
  classical
  unfold QCSD_count QCSD_solutions
  apply card_syndrome_sols_le_two_pow_n inp.n inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem QCSD_countSep_le_two_pow_n (inp : QCSD_InstanceSep) :
    QCSD_countSep inp ≤ 2 ^ inp.n := by
  classical
  unfold QCSD_countSep QCSD_solutionsSep
  apply card_syndrome_sols_le_two_pow_n inp.n inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem QCSD_countLe_le_two_pow_n (inp : QCSD_Instance) :
    QCSD_countLe inp ≤ 2 ^ inp.n := by
  classical
  unfold QCSD_countLe QCSD_solutionsLe
  apply card_syndrome_sols_le_two_pow_n inp.n inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-- Exact `2 * n`-bit strict upper bound for `QCSD_count inp` when `2 ≤ inp.n`. -/
theorem QCSD_count_lt_two_pow (inp : QCSD_Instance) (hn : 2 ≤ inp.n) :
    QCSD_count inp < 2 ^ (2 * inp.n) := by
  classical
  unfold QCSD_count QCSD_solutions
  apply card_syndrome_sols_lt_two_pow_two_mul inp.n (by omega) inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-- Exact `2 * n`-bit strict upper bound for `QCSD_countSep inp` when `2 ≤ inp.n`. -/
theorem QCSD_countSep_lt_two_pow (inp : QCSD_InstanceSep) (hn : 2 ≤ inp.n) :
    QCSD_countSep inp < 2 ^ (2 * inp.n) := by
  classical
  unfold QCSD_countSep QCSD_solutionsSep
  apply card_syndrome_sols_lt_two_pow_two_mul inp.n (by omega) inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-- Exact `2 * n`-bit strict upper bound for `QCSD_countLe inp` when `2 ≤ inp.n`. -/
theorem QCSD_countLe_lt_two_pow (inp : QCSD_Instance) (hn : 2 ≤ inp.n) :
    QCSD_countLe inp < 2 ^ (2 * inp.n) := by
  classical
  unfold QCSD_countLe QCSD_solutionsLe
  apply card_syndrome_sols_lt_two_pow_two_mul inp.n (by omega) inp.h inp.s
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

/-! ### 2C. Hamming Weight & Out-of-Range Threshold Combinatorics (`Exact`, `Sep`, `Le`) -/

theorem QCSD_wt_le_n {n : ℕ} (v : Fin n → ZMod 2) :
    QCSD_wt v ≤ n := by
  unfold QCSD_wt
  simpa using hammingNorm_le_card_fintype (x := v)

theorem QCSD_count_eq_zero_of_gt (inp : QCSD_Instance) (ht : 2 * inp.n < inp.t) :
    QCSD_count inp = 0 := by
  classical
  unfold QCSD_count QCSD_solutions
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hsol
  have hw0 := QCSD_wt_le_n p.1
  have hw1 := QCSD_wt_le_n p.2
  have hsum := hsol.2
  omega

theorem QCSD_countSep_eq_zero_of_gt (inp : QCSD_InstanceSep)
    (ht : inp.n < inp.t₀ ∨ inp.n < inp.t₁) :
    QCSD_countSep inp = 0 := by
  classical
  unfold QCSD_countSep QCSD_solutionsSep
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hsol
  have hw0 := QCSD_wt_le_n p.1
  have hw1 := QCSD_wt_le_n p.2
  have ht0 := hsol.2.1
  have ht1 := hsol.2.2
  omega

theorem QCSD_IsSolLe_clamp (inp : QCSD_Instance) (e₀ e₁ : Fin inp.n → ZMod 2) :
    QCSD_IsSolLe inp e₀ e₁ ↔
      QCSD_IsSolLe ⟨inp.n, inp.h, inp.s, min inp.t (2 * inp.n)⟩ e₀ e₁ := by
  unfold QCSD_IsSolLe
  dsimp only
  have hw0 := QCSD_wt_le_n e₀
  have hw1 := QCSD_wt_le_n e₁
  constructor <;> rintro ⟨hlin, hw⟩ <;> exact ⟨hlin, by omega⟩

theorem QCSD_countLe_clamp (inp : QCSD_Instance) :
    QCSD_countLe inp = QCSD_countLe ⟨inp.n, inp.h, inp.s, min inp.t (2 * inp.n)⟩ := by
  classical
  unfold QCSD_countLe QCSD_solutionsLe
  dsimp only
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact QCSD_IsSolLe_clamp inp p.1 p.2

/-! ### 2D. Generic & Variant-Specific Prefix Count Laws (`Exact`, `Sep`, `Le`) -/

noncomputable def prefixSolsGen {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (pre : List Bool) :
    Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)) := by
  classical
  exact sols.filter (fun p => (QCSD_encodeSolPair p.1 p.2).take pre.length = pre)

noncomputable def prefixCountGen {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (pre : List Bool) : ℕ :=
  (prefixSolsGen sols pre).card

lemma prefixCountGen_nil {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) :
    prefixCountGen sols [] = sols.card := by
  classical
  unfold prefixCountGen prefixSolsGen
  simp

lemma prefixCountGen_le_card {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (pre : List Bool) :
    prefixCountGen sols pre ≤ sols.card := by
  classical
  unfold prefixCountGen prefixSolsGen
  exact Finset.card_filter_le _ _

lemma prefixCountGen_split {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length < 2 * n) :
    prefixCountGen sols pre =
      prefixCountGen sols (pre ++ [false]) + prefixCountGen sols (pre ++ [true]) := by
  classical
  unfold prefixCountGen prefixSolsGen
  simp only [List.length_append, List.length_singleton]
  have split_list (l : List Bool) (hl : pre.length < l.length) :
      l.take pre.length = pre ↔
        l.take (pre.length + 1) = pre ++ [false] ∨
        l.take (pre.length + 1) = pre ++ [true] := by
    constructor
    · intro h
      have hnext := (List.take_concat_get' l pre.length hl).symm
      rw [h] at hnext
      cases hb : l[pre.length] with
      | false => exact Or.inl (by simpa [hb] using hnext)
      | true => exact Or.inr (by simpa [hb] using hnext)
    · intro h
      rcases h with h | h
      · have htake := congrArg (fun z : List Bool => z.take pre.length) h
        simpa [List.take_take, Nat.min_eq_left (show pre.length ≤ pre.length + 1 by omega)]
          using htake
      · have htake := congrArg (fun z : List Bool => z.take pre.length) h
        simpa [List.take_take, Nat.min_eq_left (show pre.length ≤ pre.length + 1 by omega)]
          using htake
  have hunion :
      sols.filter (fun q => (QCSD_encodeSolPair q.1 q.2).take pre.length = pre) =
        sols.filter (fun q => (QCSD_encodeSolPair q.1 q.2).take (pre.length + 1) = pre ++ [false]) ∪
        sols.filter (fun q => (QCSD_encodeSolPair q.1 q.2).take (pre.length + 1) = pre ++ [true]) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    rw [split_list (QCSD_encodeSolPair q.1 q.2) (by rw [encodeSolPair_length]; exact hp)]
    tauto
  have hdisj : Disjoint
      (sols.filter (fun q => (QCSD_encodeSolPair q.1 q.2).take (pre.length + 1) = pre ++ [false]))
      (sols.filter (fun q => (QCSD_encodeSolPair q.1 q.2).take (pre.length + 1) = pre ++ [true])) := by
    apply Finset.disjoint_left.mpr
    intro q hf ht
    have hbad := (Finset.mem_filter.mp hf).2.symm.trans (Finset.mem_filter.mp ht).2
    simp at hbad
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma prefixCountGen_greedy_step {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length < 2 * n)
    (hpos : 0 < prefixCountGen sols pre) :
    let c0 := prefixCountGen sols (pre ++ [false])
    let b := if 0 < c0 then false else true
    0 < prefixCountGen sols (pre ++ [b]) := by
  have hs := prefixCountGen_split sols pre hp
  dsimp only
  split_ifs with hc0
  · exact hc0
  · omega

lemma prefixCountGen_le_one {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length = 2 * n) :
    prefixCountGen sols pre ≤ 1 := by
  classical
  unfold prefixCountGen prefixSolsGen
  apply Finset.card_le_one.mpr
  intro p hp_mem q hq_mem
  have hp_eq : QCSD_encodeSolPair p.1 p.2 = pre := by
    have h1 := (Finset.mem_filter.mp hp_mem).2
    rwa [hp, ← encodeSolPair_length p.1 p.2, List.take_length] at h1
  have hq_eq : QCSD_encodeSolPair q.1 q.2 = pre := by
    have h1 := (Finset.mem_filter.mp hq_mem).2
    rwa [hp, ← encodeSolPair_length q.1 q.2, List.take_length] at h1
  have hdec_p := decodeSolPair_encodeSolPair p.1 p.2
  have hdec_q := decodeSolPair_encodeSolPair q.1 q.2
  rw [hp_eq] at hdec_p
  rw [hq_eq] at hdec_q
  have hsome : (some (p.1, p.2) : Option ((Fin n → ZMod 2) × (Fin n → ZMod 2))) = some (q.1, q.2) :=
    hdec_p.symm.trans hdec_q
  injection hsome

lemma prefixCountGen_eq_one_iff {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length = 2 * n) :
    prefixCountGen sols pre = 1 ↔
      ∃ e₀ e₁, QCSD_decodeSolPair n pre = some (e₀, e₁) ∧ (e₀, e₁) ∈ sols := by
  classical
  have hle1 := prefixCountGen_le_one sols pre hp
  have hpos_iff : prefixCountGen sols pre = 1 ↔ 0 < prefixCountGen sols pre := by omega
  rw [hpos_iff]
  unfold prefixCountGen prefixSolsGen
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨e₀, e₁⟩, hmem⟩
    obtain ⟨hsol, htake⟩ := Finset.mem_filter.mp hmem
    rw [hp, ← encodeSolPair_length e₀ e₁, List.take_length] at htake
    exact ⟨e₀, e₁, (decodeSolPair_eq_some_iff).mpr ⟨hp, htake⟩, hsol⟩
  · rintro ⟨e₀, e₁, hdec, hsol⟩
    obtain ⟨_, henc⟩ := (decodeSolPair_eq_some_iff).mp hdec
    refine ⟨(e₀, e₁), Finset.mem_filter.mpr ⟨hsol, ?_⟩⟩
    rw [hp, ← encodeSolPair_length e₀ e₁, List.take_length]
    exact henc

lemma prefixCountGen_eq_zero_of_gt {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : 2 * n < pre.length) :
    prefixCountGen sols pre = 0 := by
  classical
  unfold prefixCountGen prefixSolsGen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _ htake
  have hlen := congrArg List.length htake
  simp only [List.length_take, encodeSolPair_length] at hlen
  omega

/-- Valid `2 * inp.n`-bit witness predicate for `Exact` (`QCSD_Correct`). -/
def validWitness (inp : QCSD_Instance) (w : List Bool) : Prop :=
  ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSol inp e₀ e₁

/-- Valid `2 * inp.n`-bit witness predicate for `Sep` (`QCSD_CorrectSep`). -/
def validWitnessSep (inp : QCSD_InstanceSep) (w : List Bool) : Prop :=
  ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolSep inp e₀ e₁

/-- Valid `2 * inp.n`-bit witness predicate for `Le` (`QCSD_CorrectLe`). -/
def validWitnessLe (inp : QCSD_Instance) (w : List Bool) : Prop :=
  ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolLe inp e₀ e₁

/-- Prefix-pinned solution Finset and count for `Exact`. -/
noncomputable def QCSD_solutionsPrefix (inp : QCSD_Instance) (pre : List Bool) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) :=
  prefixSolsGen (QCSD_solutions inp) pre

noncomputable def QCSD_countPrefix (inp : QCSD_Instance) (pre : List Bool) : ℕ :=
  prefixCountGen (QCSD_solutions inp) pre

/-- Prefix-pinned solution Finset and count for `Sep`. -/
noncomputable def QCSD_solutionsPrefixSep (inp : QCSD_InstanceSep) (pre : List Bool) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) :=
  prefixSolsGen (QCSD_solutionsSep inp) pre

noncomputable def QCSD_countPrefixSep (inp : QCSD_InstanceSep) (pre : List Bool) : ℕ :=
  prefixCountGen (QCSD_solutionsSep inp) pre

/-- Prefix-pinned solution Finset and count for `Le`. -/
noncomputable def QCSD_solutionsPrefixLe (inp : QCSD_Instance) (pre : List Bool) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) :=
  prefixSolsGen (QCSD_solutionsLe inp) pre

noncomputable def QCSD_countPrefixLe (inp : QCSD_Instance) (pre : List Bool) : ℕ :=
  prefixCountGen (QCSD_solutionsLe inp) pre

/-! #### Variant 1 (`Exact`): Prefix Root, Binary Split, Bounds & Singleton Witness Laws -/

@[simp] theorem QCSD_countPrefix_nil (inp : QCSD_Instance) :
    QCSD_countPrefix inp [] = QCSD_count inp :=
  prefixCountGen_nil (QCSD_solutions inp)

theorem QCSD_countPrefix_le_count (inp : QCSD_Instance) (pre : List Bool) :
    QCSD_countPrefix inp pre ≤ QCSD_count inp :=
  prefixCountGen_le_card (QCSD_solutions inp) pre

theorem QCSD_countPrefix_lt_two_pow (inp : QCSD_Instance) (hn : 2 ≤ inp.n) (pre : List Bool) :
    QCSD_countPrefix inp pre < 2 ^ (2 * inp.n) :=
  Nat.lt_of_le_of_lt (QCSD_countPrefix_le_count inp pre) (QCSD_count_lt_two_pow inp hn)

theorem QCSD_countPrefix_split (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) :
    QCSD_countPrefix inp pre =
      QCSD_countPrefix inp (pre ++ [false]) + QCSD_countPrefix inp (pre ++ [true]) :=
  prefixCountGen_split (QCSD_solutions inp) pre hp

theorem QCSD_countPrefix_greedy_step (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) (hpos : 0 < QCSD_countPrefix inp pre) :
    let c0 := QCSD_countPrefix inp (pre ++ [false])
    let b := if 0 < c0 then false else true
    0 < QCSD_countPrefix inp (pre ++ [b]) :=
  prefixCountGen_greedy_step (QCSD_solutions inp) pre hp hpos

theorem QCSD_countPrefix_le_one (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefix inp pre ≤ 1 :=
  prefixCountGen_le_one (QCSD_solutions inp) pre hp

theorem QCSD_countPrefix_eq_one_iff (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefix inp pre = 1 ↔ validWitness inp pre := by
  classical
  rw [QCSD_countPrefix, prefixCountGen_eq_one_iff (QCSD_solutions inp) pre hp]
  unfold validWitness QCSD_solutions
  simp [Finset.mem_filter]

theorem QCSD_countPrefix_pos_iff (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    0 < QCSD_countPrefix inp pre ↔ validWitness inp pre := by
  have hle := QCSD_countPrefix_le_one inp pre hp
  rw [← QCSD_countPrefix_eq_one_iff inp pre hp]
  omega

/-! #### Variant 2 (`Sep`): Prefix Root, Binary Split, Bounds & Singleton Witness Laws -/

@[simp] theorem QCSD_countPrefixSep_nil (inp : QCSD_InstanceSep) :
    QCSD_countPrefixSep inp [] = QCSD_countSep inp :=
  prefixCountGen_nil (QCSD_solutionsSep inp)

theorem QCSD_countPrefixSep_le_countSep (inp : QCSD_InstanceSep) (pre : List Bool) :
    QCSD_countPrefixSep inp pre ≤ QCSD_countSep inp :=
  prefixCountGen_le_card (QCSD_solutionsSep inp) pre

theorem QCSD_countPrefixSep_lt_two_pow (inp : QCSD_InstanceSep) (hn : 2 ≤ inp.n) (pre : List Bool) :
    QCSD_countPrefixSep inp pre < 2 ^ (2 * inp.n) :=
  Nat.lt_of_le_of_lt (QCSD_countPrefixSep_le_countSep inp pre) (QCSD_countSep_lt_two_pow inp hn)

theorem QCSD_countPrefixSep_split (inp : QCSD_InstanceSep) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) :
    QCSD_countPrefixSep inp pre =
      QCSD_countPrefixSep inp (pre ++ [false]) + QCSD_countPrefixSep inp (pre ++ [true]) :=
  prefixCountGen_split (QCSD_solutionsSep inp) pre hp

theorem QCSD_countPrefixSep_greedy_step (inp : QCSD_InstanceSep) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) (hpos : 0 < QCSD_countPrefixSep inp pre) :
    let c0 := QCSD_countPrefixSep inp (pre ++ [false])
    let b := if 0 < c0 then false else true
    0 < QCSD_countPrefixSep inp (pre ++ [b]) :=
  prefixCountGen_greedy_step (QCSD_solutionsSep inp) pre hp hpos

theorem QCSD_countPrefixSep_le_one (inp : QCSD_InstanceSep) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefixSep inp pre ≤ 1 :=
  prefixCountGen_le_one (QCSD_solutionsSep inp) pre hp

theorem QCSD_countPrefixSep_eq_one_iff (inp : QCSD_InstanceSep) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefixSep inp pre = 1 ↔ validWitnessSep inp pre := by
  classical
  rw [QCSD_countPrefixSep, prefixCountGen_eq_one_iff (QCSD_solutionsSep inp) pre hp]
  unfold validWitnessSep QCSD_solutionsSep
  simp [Finset.mem_filter]

theorem QCSD_countPrefixSep_pos_iff (inp : QCSD_InstanceSep) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    0 < QCSD_countPrefixSep inp pre ↔ validWitnessSep inp pre := by
  have hle := QCSD_countPrefixSep_le_one inp pre hp
  rw [← QCSD_countPrefixSep_eq_one_iff inp pre hp]
  omega

/-! #### Variant 3 (`Le`): Prefix Root, Binary Split, Bounds & Singleton Witness Laws -/

@[simp] theorem QCSD_countPrefixLe_nil (inp : QCSD_Instance) :
    QCSD_countPrefixLe inp [] = QCSD_countLe inp :=
  prefixCountGen_nil (QCSD_solutionsLe inp)

theorem QCSD_countPrefixLe_le_countLe (inp : QCSD_Instance) (pre : List Bool) :
    QCSD_countPrefixLe inp pre ≤ QCSD_countLe inp :=
  prefixCountGen_le_card (QCSD_solutionsLe inp) pre

theorem QCSD_countPrefixLe_lt_two_pow (inp : QCSD_Instance) (hn : 2 ≤ inp.n) (pre : List Bool) :
    QCSD_countPrefixLe inp pre < 2 ^ (2 * inp.n) :=
  Nat.lt_of_le_of_lt (QCSD_countPrefixLe_le_countLe inp pre) (QCSD_countLe_lt_two_pow inp hn)

theorem QCSD_countPrefixLe_split (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) :
    QCSD_countPrefixLe inp pre =
      QCSD_countPrefixLe inp (pre ++ [false]) + QCSD_countPrefixLe inp (pre ++ [true]) :=
  prefixCountGen_split (QCSD_solutionsLe inp) pre hp

theorem QCSD_countPrefixLe_greedy_step (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length < 2 * inp.n) (hpos : 0 < QCSD_countPrefixLe inp pre) :
    let c0 := QCSD_countPrefixLe inp (pre ++ [false])
    let b := if 0 < c0 then false else true
    0 < QCSD_countPrefixLe inp (pre ++ [b]) :=
  prefixCountGen_greedy_step (QCSD_solutionsLe inp) pre hp hpos

theorem QCSD_countPrefixLe_le_one (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefixLe inp pre ≤ 1 :=
  prefixCountGen_le_one (QCSD_solutionsLe inp) pre hp

theorem QCSD_countPrefixLe_eq_one_iff (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    QCSD_countPrefixLe inp pre = 1 ↔ validWitnessLe inp pre := by
  classical
  rw [QCSD_countPrefixLe, prefixCountGen_eq_one_iff (QCSD_solutionsLe inp) pre hp]
  unfold validWitnessLe QCSD_solutionsLe
  simp [Finset.mem_filter]

theorem QCSD_countPrefixLe_pos_iff (inp : QCSD_Instance) (pre : List Bool)
    (hp : pre.length = 2 * inp.n) :
    0 < QCSD_countPrefixLe inp pre ↔ validWitnessLe inp pre := by
  have hle := QCSD_countPrefixLe_le_one inp pre hp
  rw [← QCSD_countPrefixLe_eq_one_iff inp pre hp]
  omega

/-! ### 2E. `QCSD_decodeOutputN2` & `QCSD_Correct` / `QCSD_CorrectSep` / `QCSD_CorrectLe` Packaging -/

theorem decodeOutputN2_none_of_zero (n : ℕ) (cBits rest : List Bool)
    (hc : cBits.length = 2 * n) :
    QCSD_decodeOutputN2 n (cBits ++ [false] ++ rest) = some (QCSD_bitsToNat cBits, none) := by
  unfold QCSD_decodeOutputN2
  have hlen : ¬ ((cBits ++ [false] ++ rest).length < 2 * n + 1) := by
    simp [hc]
  rw [ite_eq_right hlen]
  have hassoc : cBits ++ [false] ++ rest = cBits ++ (false :: rest) := by
    simp [List.append_assoc]
  rw [hassoc]
  have htake : (cBits ++ (false :: rest)).take (2 * n) = cBits := by
    rw [← hc, List.take_left]
  have hflag : (cBits ++ (false :: rest)).getD (2 * n) false = false := by
    rw [← hc, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
    simp
  rw [htake, hflag]
  rfl

theorem decodeOutputN2_some_of_pos (n : ℕ) (cBits w rest : List Bool)
    (hc : cBits.length = 2 * n) (hw : w.length = 2 * n) :
    QCSD_decodeOutputN2 n (cBits ++ [true] ++ w ++ rest) = some (QCSD_bitsToNat cBits, some w) := by
  unfold QCSD_decodeOutputN2
  have hlen : ¬ ((cBits ++ [true] ++ w ++ rest).length < 2 * n + 1) := by
    simp [hc, hw]
  rw [ite_eq_right hlen]
  have hassoc : cBits ++ [true] ++ w ++ rest = cBits ++ (true :: (w ++ rest)) := by
    simp [List.append_assoc]
  rw [hassoc]
  have htake : (cBits ++ (true :: (w ++ rest))).take (2 * n) = cBits := by
    rw [← hc, List.take_left]
  have hflag : (cBits ++ (true :: (w ++ rest))).getD (2 * n) false = true := by
    rw [← hc, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hdrop : ((cBits ++ (true :: (w ++ rest))).drop (2 * n + 1)).take (2 * n) = w := by
    have hdr1 : (cBits ++ (true :: (w ++ rest))).drop (2 * n + 1) = w ++ rest := by
      have hlen1 : (cBits ++ [true]).length = 2 * n + 1 := by simp [hc]
      have hassoc2 : cBits ++ (true :: (w ++ rest)) = (cBits ++ [true]) ++ (w ++ rest) := by
        simp [List.append_assoc]
      rw [hassoc2, ← hlen1, List.drop_left]
    rw [hdr1, ← hw, List.take_left]
  rw [htake, hflag, ite_eq_left rfl]
  dsimp only
  rw [hdrop, ite_eq_left hw]

theorem QCSD_Correct_of_zero (inp : QCSD_Instance) (hz : QCSD_count inp = 0) :
    QCSD_Correct inp (0, none) := by
  refine ⟨hz.symm, ⟨fun _ => rfl, fun _ => rfl⟩, fun w hw => ?_⟩
  cases hw

theorem QCSD_Correct_of_prefix_witness (inp : QCSD_Instance)
    {c : ℕ} {w : List Bool}
    (hc : c = QCSD_count inp) (hpos : 0 < c)
    (hw_len : w.length = 2 * inp.n) (hw_cnt : 0 < QCSD_countPrefix inp w) :
    QCSD_Correct inp (c, some w) := by
  refine ⟨hc, Iff.intro (fun h => by cases h) (fun h => by omega), fun w' hw' => ?_⟩
  injection hw' with heq
  subst heq
  exact (QCSD_countPrefix_pos_iff inp w hw_len).mp hw_cnt

theorem QCSD_CorrectSep_of_zero (inp : QCSD_InstanceSep) (hz : QCSD_countSep inp = 0) :
    QCSD_CorrectSep inp (0, none) := by
  refine ⟨hz.symm, ⟨fun _ => rfl, fun _ => rfl⟩, fun w hw => ?_⟩
  cases hw

theorem QCSD_CorrectSep_of_prefix_witness (inp : QCSD_InstanceSep)
    {c : ℕ} {w : List Bool}
    (hc : c = QCSD_countSep inp) (hpos : 0 < c)
    (hw_len : w.length = 2 * inp.n) (hw_cnt : 0 < QCSD_countPrefixSep inp w) :
    QCSD_CorrectSep inp (c, some w) := by
  refine ⟨hc, Iff.intro (fun h => by cases h) (fun h => by omega), fun w' hw' => ?_⟩
  injection hw' with heq
  subst heq
  exact (QCSD_countPrefixSep_pos_iff inp w hw_len).mp hw_cnt

theorem QCSD_CorrectLe_of_zero (inp : QCSD_Instance) (hz : QCSD_countLe inp = 0) :
    QCSD_CorrectLe inp (0, none) := by
  refine ⟨hz.symm, ⟨fun _ => rfl, fun _ => rfl⟩, fun w hw => ?_⟩
  cases hw

theorem QCSD_CorrectLe_of_prefix_witness (inp : QCSD_Instance)
    {c : ℕ} {w : List Bool}
    (hc : c = QCSD_countLe inp) (hpos : 0 < c)
    (hw_len : w.length = 2 * inp.n) (hw_cnt : 0 < QCSD_countPrefixLe inp w) :
    QCSD_CorrectLe inp (c, some w) := by
  refine ⟨hc, Iff.intro (fun h => by cases h) (fun h => by omega), fun w' hw' => ?_⟩
  injection hw' with heq
  subst heq
  exact (QCSD_countPrefixLe_pos_iff inp w hw_len).mp hw_cnt

end Branch5PadAndSep
