import Branch2_Algebra
import Glue_TwoLayerConv
import Branch3_Network
import Branch5_PadAndSep
import Branch7_EncodeNetSpec

namespace GlueNetConv

open QCSD.Defs
open Branch5PadAndSep

/-!
# Section 1: Bridging `Branch3` Parameters & 2-Layer Convolution to `GlueTwoLayerConv`
-/

lemma minPowExpAux_eq (b target : ℕ) :
    ∀ (fuel acc : ℕ),
      Branch3.minPowExpAux b target fuel acc = Branch2Algebra.minPowExpAux b target fuel acc
  | 0, _ => rfl
  | fuel + 1, acc => by
    simp only [Branch3.minPowExpAux, Branch2Algebra.minPowExpAux]
    split_ifs
    · rfl
    · exact minPowExpAux_eq b target fuel (acc + 1)

lemma minPowExp_eq (b target : ℕ) :
    Branch3.minPowExp b target = Branch2Algebra.minPowExp b target :=
  minPowExpAux_eq b target target 0

lemma paramK_eq (d : ℕ) : Branch3.paramK d = Branch2Algebra.paramK d :=
  minPowExp_eq 9 d

lemma paramJ_eq (d : ℕ) : Branch3.paramJ d = Branch2Algebra.paramJ d := by
  unfold Branch3.paramJ Branch2Algebra.paramJ
  rw [paramK_eq]

lemma paramM_eq (d : ℕ) : Branch3.paramM d = Branch2Algebra.paramM d := by
  unfold Branch3.paramM Branch2Algebra.paramM
  rw [paramJ_eq]

lemma paramEll_eq (d : ℕ) : Branch3.paramEll d = Branch2Algebra.paramEll d := by
  unfold Branch3.paramEll Branch2Algebra.paramEll
  rw [paramM_eq, minPowExp_eq]

lemma paramL_eq (d : ℕ) : Branch3.paramL d = Branch2Algebra.paramL d := by
  unfold Branch3.paramL Branch2Algebra.paramL
  rw [paramEll_eq]

lemma paramL1_eq (d : ℕ) : Branch3.paramL1 d = Branch2Algebra.paramL1 d := by
  unfold Branch3.paramL1 Branch2Algebra.paramL1
  rw [paramEll_eq]

lemma paramL2_eq (d : ℕ) : Branch3.paramL2 d = Branch2Algebra.paramL2 d := by
  unfold Branch3.paramL2 Branch2Algebra.paramL2
  rw [paramEll_eq]

lemma paramOmegaExp_eq (d : ℕ) :
    Branch3.paramOmegaExp d = GlueTwoLayerConv.paramOmegaExp d := by
  unfold Branch3.paramOmegaExp GlueTwoLayerConv.paramOmegaExp
  rw [paramK_eq, paramEll_eq]

lemma paramInvOmegaExp_eq (d : ℕ) :
    Branch3.paramInvOmegaExp d = GlueTwoLayerConv.paramInvOmegaExp d := by
  unfold Branch3.paramInvOmegaExp GlueTwoLayerConv.paramInvOmegaExp
  rw [paramJ_eq, paramOmegaExp_eq]

lemma twoLayerFwdSt1_eq (n : ℕ) (x : ℕ → Bool) :
    Branch3.twoLayerFwdSt1 n x = GlueTwoLayerConv.twoLayerFwdSt1 n x := by
  funext j2 q1 p
  unfold Branch3.twoLayerFwdSt1 GlueTwoLayerConv.twoLayerFwdSt1
  dsimp only
  rw [paramJ_eq, paramL1_eq, paramL2_eq, paramOmegaExp_eq]
  rfl

lemma twoLayerFwdSt2_eq (n : ℕ) (y : ℕ → ℕ → ℕ → Bool) :
    Branch3.twoLayerFwdSt2 n y = GlueTwoLayerConv.twoLayerFwdSt2 n y := by
  funext q p
  unfold Branch3.twoLayerFwdSt2 GlueTwoLayerConv.twoLayerFwdSt2
  dsimp only
  rw [paramJ_eq, paramL1_eq, paramL2_eq, paramOmegaExp_eq]
  rfl

lemma twoLayerInvSt1_eq (n : ℕ) (fc : ℕ → ℕ → Bool) :
    Branch3.twoLayerInvSt1 n fc = GlueTwoLayerConv.twoLayerInvSt1 n fc := by
  funext j2 q1 p
  unfold Branch3.twoLayerInvSt1 GlueTwoLayerConv.twoLayerInvSt1
  dsimp only
  rw [paramJ_eq, paramL1_eq, paramL2_eq, paramInvOmegaExp_eq]
  rfl

lemma twoLayerInvSt2_eq (n : ℕ) (yc : ℕ → ℕ → ℕ → Bool) :
    Branch3.twoLayerInvSt2 n yc = GlueTwoLayerConv.twoLayerInvSt2 n yc := by
  funext r p
  unfold Branch3.twoLayerInvSt2 GlueTwoLayerConv.twoLayerInvSt2
  dsimp only
  rw [paramJ_eq, paramL1_eq, paramL2_eq, paramInvOmegaExp_eq]
  rfl

lemma twoLayerPolyMulBit_eq (n : ℕ) (a b : ℕ → Bool) (k : ℕ) :
    Branch3.twoLayerPolyMulBit n a b k = GlueTwoLayerConv.twoLayerPolyMulBit n a b k := by
  unfold Branch3.twoLayerPolyMulBit GlueTwoLayerConv.twoLayerPolyMulBit
  dsimp only
  rw [twoLayerFwdSt1_eq, twoLayerFwdSt2_eq, twoLayerFwdSt1_eq, twoLayerFwdSt2_eq]
  have hrm : ∀ (J : ℕ) (u v : ℕ → Bool) (p : ℕ),
      Branch3.ringMulBits J u v p = GlueTwoLayerConv.ringMulBits J u v p :=
    fun _ _ _ _ => rfl
  have hfc :
      (fun q p => Branch3.ringMulBits (Branch3.paramJ n)
        (GlueTwoLayerConv.twoLayerFwdSt2 n (GlueTwoLayerConv.twoLayerFwdSt1 n a) q)
        (GlueTwoLayerConv.twoLayerFwdSt2 n (GlueTwoLayerConv.twoLayerFwdSt1 n b) q) p) =
      (fun q p => GlueTwoLayerConv.ringMulBits (Branch2Algebra.paramJ n)
        (GlueTwoLayerConv.twoLayerFwdSt2 n (GlueTwoLayerConv.twoLayerFwdSt1 n a) q)
        (GlueTwoLayerConv.twoLayerFwdSt2 n (GlueTwoLayerConv.twoLayerFwdSt1 n b) q) p) := by
    funext q p
    rw [paramJ_eq, hrm]
  rw [hfc, twoLayerInvSt1_eq, twoLayerInvSt2_eq, paramJ_eq, paramL_eq]

lemma twoLayerCycMul_eq (n : ℕ) (a b : Fin n → ZMod 2) (i : Fin n) :
    Branch3.twoLayerCycMul n a b i = GlueTwoLayerConv.twoLayerCycMul n a b i := by
  unfold Branch3.twoLayerCycMul GlueTwoLayerConv.twoLayerCycMul
  dsimp only
  have hz : Branch3.zmod2ToBool = Branch2Algebra.zmod2ToBool := rfl
  have hb : Branch3.boolToZMod2 = Branch2Algebra.boolToZMod2 := rfl
  rw [hz, hb, twoLayerPolyMulBit_eq, twoLayerPolyMulBit_eq]

/-- **Main Bridge Theorem (`n ≥ 1`)**: discharges `Branch3.TwoLayerConvSpec n` via
`GlueTwoLayerConv.twoLayerConvSpec_holds`. -/
theorem branch3_twoLayerConvSpec_holds {n : ℕ} (hn : 1 ≤ n) :
    Branch3.TwoLayerConvSpec n := by
  intro a b i
  rw [twoLayerCycMul_eq]
  exact GlueTwoLayerConv.twoLayerConvSpec_holds hn a b i

/-- **Unconditional Bridge Theorem (all `n : ℕ`)**: `Branch3.TwoLayerConvSpec n` holds for all `n`
(`n = 0` is vacuous on `Fin 0`; `1 ≤ n` uses `branch3_twoLayerConvSpec_holds`). -/
theorem branch3_twoLayerConvSpec_holds_all (n : ℕ) :
    Branch3.TwoLayerConvSpec n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro _ _ i
    exact i.elim0
  · exact branch3_twoLayerConvSpec_holds hn

/-!
# Section 2: Unconditional Contraction & Witness Theorems (`N_exact`, `N_le`, `N_sep`, and `padNet`)
-/

lemma QCSD_iface_eq_encodeSolPair (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) :
    Branch3.QCSD_iface n e₀ e₁ = QCSD_encodeSolPair e₀ e₁ := rfl

lemma filter_iface_card_eq_prefixCountGen {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (pre : List Bool) :
    (sols.filter (fun q => (Branch3.QCSD_iface n q.1 q.2).take pre.length = pre)).card =
      prefixCountGen sols pre := by
  unfold prefixCountGen prefixSolsGen
  congr 1

/-- Unconditional unpadded contraction for `N_exact inp pre`. -/
theorem N_exact_contraction_uncond (inp : QCSD_Instance) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (Branch3.N_exact inp pre) = QCSD_countPrefix inp pre := by
  rw [Branch3.N_exact_contraction inp pre (branch3_twoLayerConvSpec_holds_all inp.n) hpre]
  exact filter_iface_card_eq_prefixCountGen (QCSD_solutions inp) pre

/-- Unconditional unpadded contraction for `N_le inp pre`. -/
theorem N_le_contraction_uncond (inp : QCSD_Instance) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (Branch3.N_le inp pre) = QCSD_countPrefixLe inp pre := by
  rw [Branch3.N_le_contraction inp pre (branch3_twoLayerConvSpec_holds_all inp.n) hpre]
  exact filter_iface_card_eq_prefixCountGen (QCSD_solutionsLe inp) pre

/-- Unconditional unpadded contraction for `N_sep inp pre`. -/
theorem N_sep_contraction_uncond (inp : QCSD_InstanceSep) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (Branch3.N_sep inp pre) = QCSD_countPrefixSep inp pre := by
  rw [Branch3.N_sep_contraction inp pre (branch3_twoLayerConvSpec_holds_all inp.n) hpre]
  exact filter_iface_card_eq_prefixCountGen (QCSD_solutionsSep inp) pre

/-- **Unconditional Padded Contraction (`Exact`)**: `padNet W (N_exact inp pre)` contracts to
`QCSD_countPrefix inp pre` for all `W` and `pre.length ≤ 2 * inp.n`. -/
theorem padNet_N_exact_contraction (W : ℕ) (inp : QCSD_Instance) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (padNet W (Branch3.N_exact inp pre)) = QCSD_countPrefix inp pre := by
  rw [padNet_contraction2, N_exact_contraction_uncond inp pre hpre]

/-- **Unconditional Padded Contraction (`Le`)**: `padNet W (N_le inp pre)` contracts to
`QCSD_countPrefixLe inp pre` for all `W` and `pre.length ≤ 2 * inp.n`. -/
theorem padNet_N_le_contraction (W : ℕ) (inp : QCSD_Instance) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (padNet W (Branch3.N_le inp pre)) = QCSD_countPrefixLe inp pre := by
  rw [padNet_contraction2, N_le_contraction_uncond inp pre hpre]

/-- **Unconditional Padded Contraction (`Sep`)**: `padNet W (N_sep inp pre)` contracts to
`QCSD_countPrefixSep inp pre` for all `W` and `pre.length ≤ 2 * inp.n`. -/
theorem padNet_N_sep_contraction (W : ℕ) (inp : QCSD_InstanceSep) (pre : List Bool)
    (hpre : pre.length ≤ 2 * inp.n) :
    QCSD_contraction2 (padNet W (Branch3.N_sep inp pre)) = QCSD_countPrefixSep inp pre := by
  rw [padNet_contraction2, N_sep_contraction_uncond inp pre hpre]

/-- Root (`pre = []`) unconditional padded contraction for `Exact`. -/
theorem padNet_N_exact_contraction_nil (W : ℕ) (inp : QCSD_Instance) :
    QCSD_contraction2 (padNet W (Branch3.N_exact inp [])) = QCSD_count inp := by
  rw [padNet_N_exact_contraction W inp [] (by simp), QCSD_countPrefix_nil]

/-- Root (`pre = []`) unconditional padded contraction for `Le`. -/
theorem padNet_N_le_contraction_nil (W : ℕ) (inp : QCSD_Instance) :
    QCSD_contraction2 (padNet W (Branch3.N_le inp [])) = QCSD_countLe inp := by
  rw [padNet_N_le_contraction W inp [] (by simp), QCSD_countPrefixLe_nil]

/-- Root (`pre = []`) unconditional padded contraction for `Sep`. -/
theorem padNet_N_sep_contraction_nil (W : ℕ) (inp : QCSD_InstanceSep) :
    QCSD_contraction2 (padNet W (Branch3.N_sep inp [])) = QCSD_countSep inp := by
  rw [padNet_N_sep_contraction W inp [] (by simp), QCSD_countPrefixSep_nil]

/-- Full-prefix (`w.length = 2 * inp.n`) witness equivalence for `padNet W (N_exact inp w)`. -/
theorem padNet_N_exact_full_prefix_iff (W : ℕ) (inp : QCSD_Instance) (w : List Bool)
    (hw : w.length = 2 * inp.n) :
    (0 < QCSD_contraction2 (padNet W (Branch3.N_exact inp w)) ↔ validWitness inp w) ∧
    (QCSD_contraction2 (padNet W (Branch3.N_exact inp w)) = 1 ↔ validWitness inp w) ∧
    QCSD_contraction2 (padNet W (Branch3.N_exact inp w)) ≤ 1 := by
  rw [padNet_N_exact_contraction W inp w (le_of_eq hw)]
  exact ⟨QCSD_countPrefix_pos_iff inp w hw,
         QCSD_countPrefix_eq_one_iff inp w hw,
         QCSD_countPrefix_le_one inp w hw⟩

/-- Full-prefix (`w.length = 2 * inp.n`) witness equivalence for `padNet W (N_le inp w)`. -/
theorem padNet_N_le_full_prefix_iff (W : ℕ) (inp : QCSD_Instance) (w : List Bool)
    (hw : w.length = 2 * inp.n) :
    (0 < QCSD_contraction2 (padNet W (Branch3.N_le inp w)) ↔ validWitnessLe inp w) ∧
    (QCSD_contraction2 (padNet W (Branch3.N_le inp w)) = 1 ↔ validWitnessLe inp w) ∧
    QCSD_contraction2 (padNet W (Branch3.N_le inp w)) ≤ 1 := by
  rw [padNet_N_le_contraction W inp w (le_of_eq hw)]
  exact ⟨QCSD_countPrefixLe_pos_iff inp w hw,
         QCSD_countPrefixLe_eq_one_iff inp w hw,
         QCSD_countPrefixLe_le_one inp w hw⟩

/-- Full-prefix (`w.length = 2 * inp.n`) witness equivalence for `padNet W (N_sep inp w)`. -/
theorem padNet_N_sep_full_prefix_iff (W : ℕ) (inp : QCSD_InstanceSep) (w : List Bool)
    (hw : w.length = 2 * inp.n) :
    (0 < QCSD_contraction2 (padNet W (Branch3.N_sep inp w)) ↔ validWitnessSep inp w) ∧
    (QCSD_contraction2 (padNet W (Branch3.N_sep inp w)) = 1 ↔ validWitnessSep inp w) ∧
    QCSD_contraction2 (padNet W (Branch3.N_sep inp w)) ≤ 1 := by
  rw [padNet_N_sep_contraction W inp w (le_of_eq hw)]
  exact ⟨QCSD_countPrefixSep_pos_iff inp w hw,
         QCSD_countPrefixSep_eq_one_iff inp w hw,
         QCSD_countPrefixSep_le_one inp w hw⟩

/-!
# Section 3: Unconditional Edge-Count Bounds, `QCSD_TCAdmissible`, and `padNet` `QCSD_TCClass2`
-/

theorem padNet_buildQCSDNet_edgeCount_bounds (W mode : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    2 * n ≤ QCSD_edgeCount2 (padNet W (Branch3.buildQCSDNet mode n h s t0 t1 pre)) ∧
    QCSD_edgeCount2 (padNet W (Branch3.buildQCSDNet mode n h s t0 t1 pre)) ≤ 420 * n := by
  rw [padNet_edgeCount2]
  exact Branch3.netEdgeCount_bounds hn

theorem padNet_N_exact_edgeCount_bounds (W : ℕ) (inp : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (padNet W (Branch3.N_exact inp pre)) ∧
    QCSD_edgeCount2 (padNet W (Branch3.N_exact inp pre)) ≤ 420 * inp.n := by
  rw [padNet_edgeCount2]
  exact Branch3.N_exact_edgeCount_bounds inp pre hn

theorem padNet_N_le_edgeCount_bounds (W : ℕ) (inp : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (padNet W (Branch3.N_le inp pre)) ∧
    QCSD_edgeCount2 (padNet W (Branch3.N_le inp pre)) ≤ 420 * inp.n := by
  rw [padNet_edgeCount2]
  exact Branch3.N_le_edgeCount_bounds inp pre hn

theorem padNet_N_sep_edgeCount_bounds (W : ℕ) (inp : QCSD_InstanceSep) (pre : List Bool)
    (hn : 1 ≤ inp.n) :
    2 * inp.n ≤ QCSD_edgeCount2 (padNet W (Branch3.N_sep inp pre)) ∧
    QCSD_edgeCount2 (padNet W (Branch3.N_sep inp pre)) ≤ 420 * inp.n := by
  rw [padNet_edgeCount2]
  exact Branch3.N_sep_edgeCount_bounds inp pre hn

/-- Explicit `QCSD_TCAdmissible` proof for unpadded `Branch3` parameters. -/
theorem branch3_tcAdmissible :
    QCSD_TCAdmissible Branch3.tcCDelta 1 Branch3.tcKm 5 Branch3.tcKcost 2 Branch3.tcKpred := by
  refine ⟨?_, by decide, by decide, by decide⟩
  unfold Branch3.tcCDelta
  norm_num

/-- Explicit `QCSD_TCAdmissible` proof for `padNet W` parameters under any polynomial bound
`W ≤ C_pad * n ^ d_pad`. -/
theorem padNet_tcAdmissible (C_pad d_pad : ℕ) :
    QCSD_TCAdmissible Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 (max Branch3.tcKpred 1) :=
  padNet_TCAdmissible branch3_tcAdmissible

/-- Simplified `padNet_tcAdmissible` using `max Branch3.tcKpred 1 = Branch3.tcKpred`. -/
theorem padNet_tcAdmissible_simp (C_pad d_pad : ℕ) :
    QCSD_TCAdmissible Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 Branch3.tcKpred :=
  padNet_tcAdmissible C_pad d_pad

/-- Unified `QCSD_TCClass2` membership for `padNet W (buildQCSDNet mode n h s t0 t1 pre)`. -/
theorem padNet_buildQCSDNet_tcClass2 {C_pad d_pad W n : ℕ}
    (hn : 1 ≤ n) (hW : W ≤ C_pad * n ^ d_pad)
    (mode : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_TCClass2 Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 Branch3.tcKpred
      (padNet W (Branch3.buildQCSDNet mode n h s t0 t1 pre)) := by
  have hS := (Branch3.netEdgeCount_bounds hn).1
  have hn_le : n ≤ QCSD_edgeCount2 (Branch3.buildQCSDNet mode n h s t0 t1 pre) := by
    change n ≤ Branch3.netEdgeCount n
    omega
  exact padNet_mem_TCClass2_of_le
    (Branch3.buildQCSDNet_tcClass2 hn mode h s t0 t1 pre) hn_le hW

/-- **Padded `QCSD_TCClass2` Membership (`Exact`)**: holds for any polynomial `W ≤ C_pad * inp.n ^ d_pad`. -/
theorem padNet_N_exact_tcClass2 {C_pad d_pad W : ℕ}
    (inp : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ inp.n) (hW : W ≤ C_pad * inp.n ^ d_pad) :
    QCSD_TCClass2 Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 Branch3.tcKpred
      (padNet W (Branch3.N_exact inp pre)) :=
  padNet_buildQCSDNet_tcClass2 hn hW 0 inp.h inp.s inp.t 0 pre

/-- **Padded `QCSD_TCClass2` Membership (`Le`)**: holds for any polynomial `W ≤ C_pad * inp.n ^ d_pad`. -/
theorem padNet_N_le_tcClass2 {C_pad d_pad W : ℕ}
    (inp : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ inp.n) (hW : W ≤ C_pad * inp.n ^ d_pad) :
    QCSD_TCClass2 Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 Branch3.tcKpred
      (padNet W (Branch3.N_le inp pre)) :=
  padNet_buildQCSDNet_tcClass2 hn hW 1 inp.h inp.s inp.t 0 pre

/-- **Padded `QCSD_TCClass2` Membership (`Sep`)**: holds for any polynomial `W ≤ C_pad * inp.n ^ d_pad`. -/
theorem padNet_N_sep_tcClass2 {C_pad d_pad W : ℕ}
    (inp : QCSD_InstanceSep) (pre : List Bool)
    (hn : 1 ≤ inp.n) (hW : W ≤ C_pad * inp.n ^ d_pad) :
    QCSD_TCClass2 Branch3.tcCDelta
      (max 1 d_pad) (Branch3.tcKm + C_pad)
      (max 5 d_pad) (Branch3.tcKcost + 7 * C_pad)
      2 Branch3.tcKpred
      (padNet W (Branch3.N_sep inp pre)) :=
  padNet_buildQCSDNet_tcClass2 hn hW 2 inp.h inp.s inp.t₀ inp.t₁ pre

/-!
# Section 4: `QCSD_encodeNet2` Stream Split & Circuit Constructor Bridges (`Branch3` ↔ `Branch7EncodeSpec`)
-/

lemma buildQCSDNet_ends_eq_rawEnds (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (e : Fin (Branch3.buildQCSDNet mode n h s t0 t1 pre).k) :
    (((Branch3.buildQCSDNet mode n h s t0 t1 pre).ends e).1.val,
     ((Branch3.buildQCSDNet mode n h s t0 t1 pre).ends e).2.val) =
      Branch3.rawEnds n e.val := by
  change ((Branch3.rawEnds n e.val).1, (Branch3.rawEnds n e.val).2) = Branch3.rawEnds n e.val
  exact Prod.eta (Branch3.rawEnds n e.val)

lemma buildQCSDNet_pred_eq_rawPred (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre : List Bool) (v : Fin (Branch3.buildQCSDNet mode n h s t0 t1 pre).m) :
    (Branch3.buildQCSDNet mode n h s t0 t1 pre).pred v =
      Branch3.rawPred mode n h s t0 t1 pre v.val := rfl

/-- Exact `List.range` bit-stream representation of `QCSD_encodeNet2 (padNet padV (buildQCSDNet ...))`. -/
theorem encodeNet2_padNet_buildQCSDNet_stream_eq
    (padV mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_encodeNet2 (padNet padV (Branch3.buildQCSDNet mode n h s t0 t1 pre)) =
      List.replicate (Branch3.netVertCount n + padV) true ++ [false] ++
      QCSD_natToUnary (Branch3.netEdgeCount n) ++
      (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
        QCSD_natToUnary (Branch3.rawEnds n e).1 ++ QCSD_natToUnary (Branch3.rawEnds n e).2) ++
      (List.range (Branch3.netVertCount n)).flatMap (fun v =>
        QCSD_encodeCircuit (Branch3.rawPred mode n h s t0 t1 pre v)) ++
      (List.range padV).flatMap (fun _ => [false, true, false, false, false, true]) :=
  Branch7EncodeSpec.encodeNet2_padNet_stream_eq padV
    (Branch3.buildQCSDNet mode n h s t0 t1 pre)
    (Branch3.rawEnds n)
    (Branch3.rawPred mode n h s t0 t1 pre)
    (buildQCSDNet_ends_eq_rawEnds mode n h s t0 t1 pre)
    (buildQCSDNet_pred_eq_rawPred mode n h s t0 t1 pre)

/-- General workspace-split bit-stream formula (`W ≤ netVertCount n + padV`) for `buildQCSDNet`. -/
theorem encodeNet2_padNet_buildQCSDNet_stream_split
    (padV W mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (hW : W ≤ Branch3.netVertCount n + padV) :
    QCSD_encodeNet2 (padNet padV (Branch3.buildQCSDNet mode n h s t0 t1 pre)) =
      List.replicate W true ++
      (List.replicate (Branch3.netVertCount n + padV - W) true ++ [false] ++
       QCSD_natToUnary (Branch3.netEdgeCount n) ++
       (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
         QCSD_natToUnary (Branch3.rawEnds n e).1 ++ QCSD_natToUnary (Branch3.rawEnds n e).2) ++
       (List.range (Branch3.netVertCount n)).flatMap (fun v =>
         QCSD_encodeCircuit (Branch3.rawPred mode n h s t0 t1 pre v)) ++
       (List.range padV).flatMap (fun _ => [false, true, false, false, false, true])) :=
  Branch7EncodeSpec.encodeNet2_padNet_stream_split padV W
    (Branch3.buildQCSDNet mode n h s t0 t1 pre)
    (Branch3.rawEnds n)
    (Branch3.rawPred mode n h s t0 t1 pre)
    hW
    (buildQCSDNet_ends_eq_rawEnds mode n h s t0 t1 pre)
    (buildQCSDNet_pred_eq_rawPred mode n h s t0 t1 pre)

/-- **Exact `padV = W` Workspace-Split Bit-Stream Formula for `buildQCSDNet`**:
applies `Branch7EncodeSpec.encodeNet2_padNet_stream_split_exact` directly to
`Branch3.buildQCSDNet mode n h s t0 t1 pre`. -/
theorem encodeNet2_padNet_buildQCSDNet_stream_split_exact
    (W mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.buildQCSDNet mode n h s t0 t1 pre)) =
      List.replicate W true ++
      (List.replicate (Branch3.netVertCount n) true ++ [false] ++
       QCSD_natToUnary (Branch3.netEdgeCount n) ++
       (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
         QCSD_natToUnary (Branch3.rawEnds n e).1 ++ QCSD_natToUnary (Branch3.rawEnds n e).2) ++
       (List.range (Branch3.netVertCount n)).flatMap (fun v =>
         QCSD_encodeCircuit (Branch3.rawPred mode n h s t0 t1 pre v)) ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) :=
  Branch7EncodeSpec.encodeNet2_padNet_stream_split_exact W
    (Branch3.buildQCSDNet mode n h s t0 t1 pre)
    (Branch3.rawEnds n)
    (Branch3.rawPred mode n h s t0 t1 pre)
    (buildQCSDNet_ends_eq_rawEnds mode n h s t0 t1 pre)
    (buildQCSDNet_pred_eq_rawPred mode n h s t0 t1 pre)

theorem encodeNet2_padNet_N_exact_stream_split_exact
    (W : ℕ) (inp : QCSD_Instance) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_exact inp pre)) =
      List.replicate W true ++
      (List.replicate (Branch3.netVertCount inp.n) true ++ [false] ++
       QCSD_natToUnary (Branch3.netEdgeCount inp.n) ++
       (List.range (Branch3.netEdgeCount inp.n)).flatMap (fun e =>
         QCSD_natToUnary (Branch3.rawEnds inp.n e).1 ++ QCSD_natToUnary (Branch3.rawEnds inp.n e).2) ++
       (List.range (Branch3.netVertCount inp.n)).flatMap (fun v =>
         QCSD_encodeCircuit (Branch3.rawPred 0 inp.n inp.h inp.s inp.t 0 pre v)) ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) :=
  encodeNet2_padNet_buildQCSDNet_stream_split_exact W 0 inp.n inp.h inp.s inp.t 0 pre

theorem encodeNet2_padNet_N_le_stream_split_exact
    (W : ℕ) (inp : QCSD_Instance) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_le inp pre)) =
      List.replicate W true ++
      (List.replicate (Branch3.netVertCount inp.n) true ++ [false] ++
       QCSD_natToUnary (Branch3.netEdgeCount inp.n) ++
       (List.range (Branch3.netEdgeCount inp.n)).flatMap (fun e =>
         QCSD_natToUnary (Branch3.rawEnds inp.n e).1 ++ QCSD_natToUnary (Branch3.rawEnds inp.n e).2) ++
       (List.range (Branch3.netVertCount inp.n)).flatMap (fun v =>
         QCSD_encodeCircuit (Branch3.rawPred 1 inp.n inp.h inp.s inp.t 0 pre v)) ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) :=
  encodeNet2_padNet_buildQCSDNet_stream_split_exact W 1 inp.n inp.h inp.s inp.t 0 pre

theorem encodeNet2_padNet_N_sep_stream_split_exact
    (W : ℕ) (inp : QCSD_InstanceSep) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_sep inp pre)) =
      List.replicate W true ++
      (List.replicate (Branch3.netVertCount inp.n) true ++ [false] ++
       QCSD_natToUnary (Branch3.netEdgeCount inp.n) ++
       (List.range (Branch3.netEdgeCount inp.n)).flatMap (fun e =>
         QCSD_natToUnary (Branch3.rawEnds inp.n e).1 ++ QCSD_natToUnary (Branch3.rawEnds inp.n e).2) ++
       (List.range (Branch3.netVertCount inp.n)).flatMap (fun v =>
         QCSD_encodeCircuit (Branch3.rawPred 2 inp.n inp.h inp.s inp.t₀ inp.t₁ pre v)) ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) :=
  encodeNet2_padNet_buildQCSDNet_stream_split_exact W 2 inp.n inp.h inp.s inp.t₀ inp.t₁ pre

/-! ### Exact Equality of `Branch3` Circuit Constructors with `Branch7EncodeSpec` -/

lemma emitXorListAux_eq :
    ∀ (gs : List QCSD_Gate) (acc : ℕ) (ws : List ℕ),
      Branch3.emitXorListAux gs acc ws = Branch7EncodeSpec.emitXorListAux gs acc ws
  | _, _, [] => rfl
  | gs, acc, w :: ws => by
    simp only [Branch3.emitXorListAux, Branch7EncodeSpec.emitXorListAux]
    exact emitXorListAux_eq (Branch3.emitXor gs acc w).1 (Branch3.emitXor gs acc w).2 ws

lemma emitXorList_eq (gs : List QCSD_Gate) (ws : List ℕ) :
    Branch3.emitXorList gs ws = Branch7EncodeSpec.emitXorList gs ws := by
  unfold Branch3.emitXorList Branch7EncodeSpec.emitXorList
  exact emitXorListAux_eq _ _ ws

lemma emitAllAux_eq :
    ∀ (gs : List QCSD_Gate) (acc : ℕ) (ws : List ℕ),
      Branch3.emitAllAux gs acc ws = Branch7EncodeSpec.emitAllAux gs acc ws
  | _, _, [] => rfl
  | gs, acc, w :: ws => by
    simp only [Branch3.emitAllAux, Branch7EncodeSpec.emitAllAux]
    exact emitAllAux_eq (Branch3.emitConj gs acc w).1 (Branch3.emitConj gs acc w).2 ws

lemma emitAll_eq (gs : List QCSD_Gate) (ws : List ℕ) :
    Branch3.emitAll gs ws = Branch7EncodeSpec.emitAll gs ws := by
  unfold Branch3.emitAll Branch7EncodeSpec.emitAll
  exact emitAllAux_eq _ _ ws

lemma emitParityChecks_eq :
    ∀ (gs : List QCSD_Gate) (specs : List (ℕ × List ℕ)),
      Branch3.emitParityChecks gs specs = Branch7EncodeSpec.emitParityChecks gs specs
  | _, [] => rfl
  | gs, (outW, inWs) :: rest => by
    simp only [Branch3.emitParityChecks, Branch7EncodeSpec.emitParityChecks]
    rw [emitXorList_eq]
    have heq :
        Branch3.emitEq (Branch7EncodeSpec.emitXorList gs inWs).1 outW
          (Branch7EncodeSpec.emitXorList gs inWs).2 =
        Branch7EncodeSpec.emitEq (Branch7EncodeSpec.emitXorList gs inWs).1 outW
          (Branch7EncodeSpec.emitXorList gs inWs).2 := rfl
    rw [heq, emitParityChecks_eq]

lemma emitPairConjs_eq :
    ∀ (gs : List QCSD_Gate) (pairs : List (ℕ × ℕ)),
      Branch3.emitPairConjs gs pairs = Branch7EncodeSpec.emitPairConjs gs pairs
  | _, [] => rfl
  | gs, (a, b) :: rest => by
    simp only [Branch3.emitPairConjs, Branch7EncodeSpec.emitPairConjs]
    exact emitPairConjs_eq (Branch3.emitConj gs a b).1 rest

theorem branch3_constCircuit_eq (numIn : ℕ) (b : Bool) :
    Branch3.constCircuit numIn b = Branch7EncodeSpec.constCircuit numIn b := rfl

theorem branch3_pinBitCircuit_eq (opt : Option Bool) :
    Branch3.pinBitCircuit opt = Branch7EncodeSpec.pinBitCircuit opt := by
  cases opt <;> rfl

theorem branch3_guardedBitCircuit_eq (guard target : Bool) :
    Branch3.guardedBitCircuit guard target = Branch7EncodeSpec.guardedBitCircuit guard target := by
  cases guard <;> rfl

theorem branch3_synCheckCircuit_eq (target : Bool) :
    Branch3.synCheckCircuit target = Branch7EncodeSpec.synCheckCircuit target := rfl

theorem branch3_fullAdderCircuit_eq :
    Branch3.fullAdderCircuit = Branch7EncodeSpec.fullAdderCircuit := rfl

theorem branch3_sepFullAdderCircuit_eq (guard t0Bit t1Bit : Bool) :
    Branch3.sepFullAdderCircuit guard t0Bit t1Bit =
      Branch7EncodeSpec.sepFullAdderCircuit guard t0Bit t1Bit := by
  cases guard <;> rfl

theorem branch3_exactCmpStepCircuit_eq (guard tBit : Bool) :
    Branch3.exactCmpStepCircuit guard tBit = Branch7EncodeSpec.exactCmpStepCircuit guard tBit := by
  cases guard <;> rfl

theorem branch3_borrowStepCircuit_eq (tBit : Bool) :
    Branch3.borrowStepCircuit tBit = Branch7EncodeSpec.borrowStepCircuit tBit := rfl

theorem branch3_sepCmpStepCircuit_eq :
    Branch3.sepCmpStepCircuit = Branch7EncodeSpec.sepCmpStepCircuit := rfl

theorem branch3_linearMapCheckCircuit_eq (numIn numOut : ℕ) (mat : ℕ → ℕ → Bool) :
    Branch3.linearMapCheckCircuit numIn numOut mat =
      Branch7EncodeSpec.linearMapCheckCircuit numIn numOut mat := by
  unfold Branch3.linearMapCheckCircuit Branch7EncodeSpec.linearMapCheckCircuit
  dsimp only
  have hinit : Branch3.initInputs (numIn + numOut) = Branch7EncodeSpec.initInputs (numIn + numOut) := rfl
  rw [hinit, emitParityChecks_eq, emitAll_eq]

theorem branch3_bilinearMapCheckCircuit_eq (n1 n2 nOut : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) :
    Branch3.bilinearMapCheckCircuit n1 n2 nOut tensor =
      Branch7EncodeSpec.bilinearMapCheckCircuit n1 n2 nOut tensor := by
  unfold Branch3.bilinearMapCheckCircuit Branch7EncodeSpec.bilinearMapCheckCircuit
  dsimp only
  have hinit : Branch3.initInputs (n1 + n2 + nOut) = Branch7EncodeSpec.initInputs (n1 + n2 + nOut) := rfl
  have hpairs : Branch3.bilinearPairs n1 n2 = Branch7EncodeSpec.bilinearPairs n1 n2 := rfl
  rw [hinit, hpairs, emitPairConjs_eq, emitParityChecks_eq, emitAll_eq]

end GlueNetConv
