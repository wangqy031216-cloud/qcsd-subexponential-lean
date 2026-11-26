import Branch3_Network
import Branch5_PadAndSep
import Branch6_EncoderMacros
import Branch6b_ParseAndEdges
import Branch7_EncodeNetSpec
import Branch8_CircuitEmitters
import Branch8b_TailCircuitsEmit
import Glue_NetworkAndConv

namespace GlueMnetRMProg

open QCSD.Defs
open Branch5PadAndSep
open Branch6Encoder

/-!
# Section 1: Stream-Equivalence Bridges (`Branch3` ↔ `Branch6Encoder` ↔ `Branch8CircuitEmit` ↔ `Branch8bTail`)

Zero custom `structure`, `inductive`, or `class` declarations; zero `instance` declarations.
-/

lemma minPowExpAux_b6_eq_b3 (b target : ℕ) :
    ∀ (fuel acc : ℕ),
      Branch6Encoder.minPowExpAux b target fuel acc = Branch3.minPowExpAux b target fuel acc
  | 0, _ => rfl
  | fuel + 1, acc => by
    simp only [Branch6Encoder.minPowExpAux, Branch3.minPowExpAux]
    split_ifs
    · rfl
    · exact minPowExpAux_b6_eq_b3 b target fuel (acc + 1)

lemma minPowExp_b6_eq_b3 (b target : ℕ) :
    Branch6Encoder.minPowExp b target = Branch3.minPowExp b target :=
  minPowExpAux_b6_eq_b3 b target target 0

lemma paramK_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramK d = Branch3.paramK d :=
  minPowExp_b6_eq_b3 9 d

lemma paramJ_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramJ d = Branch3.paramJ d := by
  unfold Branch6Encoder.paramJ Branch3.paramJ; rw [paramK_b6_eq_b3]

lemma paramM_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramM d = Branch3.paramM d := by
  unfold Branch6Encoder.paramM Branch3.paramM; rw [paramJ_b6_eq_b3]

lemma paramEll_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramEll d = Branch3.paramEll d := by
  unfold Branch6Encoder.paramEll Branch3.paramEll; rw [paramM_b6_eq_b3, minPowExp_b6_eq_b3]

lemma paramL_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramL d = Branch3.paramL d := by
  unfold Branch6Encoder.paramL Branch3.paramL; rw [paramEll_b6_eq_b3]

lemma paramL1_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramL1 d = Branch3.paramL1 d := by
  unfold Branch6Encoder.paramL1 Branch3.paramL1; rw [paramEll_b6_eq_b3]

lemma paramL2_b6_eq_b3 (d : ℕ) : Branch6Encoder.paramL2 d = Branch3.paramL2 d := by
  unfold Branch6Encoder.paramL2 Branch3.paramL2; rw [paramEll_b6_eq_b3]

lemma paramOmegaExp_b6_eq_b3 (d : ℕ) :
    Branch6Encoder.paramOmegaExp d = Branch3.paramOmegaExp d := by
  unfold Branch6Encoder.paramOmegaExp Branch3.paramOmegaExp
  rw [paramK_b6_eq_b3, paramEll_b6_eq_b3]

lemma paramInvOmegaExp_b6_eq_b3 (d : ℕ) :
    Branch6Encoder.paramInvOmegaExp d = Branch3.paramInvOmegaExp d := by
  unfold Branch6Encoder.paramInvOmegaExp Branch3.paramInvOmegaExp
  rw [paramJ_b6_eq_b3, paramOmegaExp_b6_eq_b3]

lemma treeLog_b6_eq_b3 (d : ℕ) : Branch6Encoder.treeLog d = Branch3.treeLog d := by
  unfold Branch6Encoder.treeLog Branch3.treeLog; rw [minPowExp_b6_eq_b3]

lemma treeM_b6_eq_b3 (d : ℕ) : Branch6Encoder.treeM d = Branch3.treeM d := by
  unfold Branch6Encoder.treeM Branch3.treeM; rw [treeLog_b6_eq_b3]

lemma treeEdgeOff_b6_eq_b3 (r : ℕ) :
    ∀ k : ℕ, Branch6Encoder.treeEdgeOff r k = Branch3.treeEdgeOff r k
  | 0 => rfl
  | 1 => rfl
  | j + 2 => by
    change Branch6Encoder.treeEdgeOff r (j + 1) + (2 * (j + 1) + 1) * 2 ^ (r - (j + 1)) =
      Branch3.treeEdgeOff r (j + 1) + (2 * (j + 1) + 1) * 2 ^ (r - (j + 1))
    rw [treeEdgeOff_b6_eq_b3 r (j + 1)]

lemma treeVertOff_b6_eq_b3 (r : ℕ) :
    ∀ k : ℕ, Branch6Encoder.treeVertOff r k = Branch3.treeVertOff r k
  | 0 => rfl
  | 1 => rfl
  | j + 2 => by
    change Branch6Encoder.treeVertOff r (j + 1) + (j + 1 + 1) * 2 ^ (r - (j + 1)) =
      Branch3.treeVertOff r (j + 1) + (j + 1 + 1) * 2 ^ (r - (j + 1))
    rw [treeVertOff_b6_eq_b3 r (j + 1)]

lemma decodeTreeEdgeAux_b6_eq_b3 (r : ℕ) :
    ∀ (fuel rem j : ℕ),
      Branch6Encoder.decodeTreeEdgeAux r rem fuel j = Branch3.decodeTreeEdgeAux r rem fuel j
  | 0, _, _ => rfl
  | fuel + 1, rem, j => by
    simp only [Branch6Encoder.decodeTreeEdgeAux, Branch3.decodeTreeEdgeAux]
    split_ifs
    · rfl
    · exact decodeTreeEdgeAux_b6_eq_b3 r fuel _ (j + 1)

lemma decodeTreeEdge_b6_eq_b3 (r locE : ℕ) :
    Branch6Encoder.decodeTreeEdge r locE = Branch3.decodeTreeEdge r locE :=
  decodeTreeEdgeAux_b6_eq_b3 r r locE 1

lemma decodeTreeVertAux_b8b_eq_b3 (r : ℕ) :
    ∀ (fuel rem j : ℕ),
      Branch8bTail.decodeTreeVertAux r rem fuel j = Branch3.decodeTreeVertAux r rem fuel j
  | 0, _, _ => rfl
  | fuel + 1, rem, j => by
    simp only [Branch8bTail.decodeTreeVertAux, Branch3.decodeTreeVertAux]
    split_ifs
    · rfl
    · exact decodeTreeVertAux_b8b_eq_b3 r fuel _ (j + 1)

lemma decodeTreeVert_b8b_eq_b3 (r locV : ℕ) :
    Branch8bTail.decodeTreeVert r locV = Branch3.decodeTreeVert r locV :=
  decodeTreeVertAux_b8b_eq_b3 r r locV 1

lemma netV0_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV0 n = Branch3.netV0 n := rfl
lemma netV1_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV1 n = Branch3.netV1 n := rfl
lemma netV2_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV2 n = Branch3.netV2 n := rfl
lemma netV3_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV3 n = Branch3.netV3 n := rfl
lemma netV4_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV4 n = Branch3.netV4 n := by
  unfold Branch6Encoder.netV4 Branch3.netV4; rw [paramL2_b6_eq_b3]
lemma netV5_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV5 n = Branch3.netV5 n := by
  unfold Branch6Encoder.netV5 Branch3.netV5; rw [paramL2_b6_eq_b3, paramL1_b6_eq_b3]
lemma netV6_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV6 n = Branch3.netV6 n := by
  unfold Branch6Encoder.netV6 Branch3.netV6; rw [paramL2_b6_eq_b3, paramL1_b6_eq_b3]
lemma netV7_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV7 n = Branch3.netV7 n := by
  unfold Branch6Encoder.netV7 Branch3.netV7; rw [paramL2_b6_eq_b3, paramL1_b6_eq_b3]
lemma netV8_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV8 n = Branch3.netV8 n := by
  unfold Branch6Encoder.netV8 Branch3.netV8; rw [netV7_b6_eq_b3, paramL_b6_eq_b3]
lemma netV9_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV9 n = Branch3.netV9 n := by
  unfold Branch6Encoder.netV9 Branch3.netV9; rw [netV8_b6_eq_b3, paramL2_b6_eq_b3]
lemma netV10_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV10 n = Branch3.netV10 n := by
  unfold Branch6Encoder.netV10 Branch3.netV10; rw [netV9_b6_eq_b3, paramL1_b6_eq_b3]
lemma netV11_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV11 n = Branch3.netV11 n := by
  unfold Branch6Encoder.netV11 Branch3.netV11; rw [netV10_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netV12_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV12 n = Branch3.netV12 n := by
  unfold Branch6Encoder.netV12 Branch3.netV12; rw [netV11_b6_eq_b3]
lemma netV13_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV13 n = Branch3.netV13 n := by
  unfold Branch6Encoder.netV13 Branch3.netV13; rw [netV12_b6_eq_b3]
lemma netV14_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV14 n = Branch3.netV14 n := by
  unfold Branch6Encoder.netV14 Branch3.netV14; rw [netV13_b6_eq_b3, treeM_b6_eq_b3]
lemma netV15_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV15 n = Branch3.netV15 n := by
  unfold Branch6Encoder.netV15 Branch3.netV15; rw [netV14_b6_eq_b3, treeM_b6_eq_b3]
lemma netV16_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV16 n = Branch3.netV16 n := by
  unfold Branch6Encoder.netV16 Branch3.netV16
  rw [netV15_b6_eq_b3, treeLog_b6_eq_b3, treeVertOff_b6_eq_b3]
lemma netV17_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV17 n = Branch3.netV17 n := by
  unfold Branch6Encoder.netV17 Branch3.netV17; rw [netV16_b6_eq_b3]
lemma netV18_b6_eq_b3 (n : ℕ) : Branch6Encoder.netV18 n = Branch3.netV18 n := by
  unfold Branch6Encoder.netV18 Branch3.netV18; rw [netV17_b6_eq_b3, treeLog_b6_eq_b3]
lemma netVertCount_b6_eq_b3 (n : ℕ) : Branch6Encoder.netVertCount n = Branch3.netVertCount n := by
  unfold Branch6Encoder.netVertCount Branch3.netVertCount; rw [netV18_b6_eq_b3]

lemma netE0_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE0 n = Branch3.netE0 n := rfl
lemma netE1_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE1 n = Branch3.netE1 n := rfl
lemma netE2_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE2 n = Branch3.netE2 n := rfl
lemma netE3_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE3 n = Branch3.netE3 n := by
  unfold Branch6Encoder.netE3 Branch3.netE3; rw [treeM_b6_eq_b3]
lemma netE4_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE4 n = Branch3.netE4 n := by
  unfold Branch6Encoder.netE4 Branch3.netE4; rw [netE3_b6_eq_b3]
lemma netE5_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE5 n = Branch3.netE5 n := by
  unfold Branch6Encoder.netE5 Branch3.netE5; rw [netE4_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE6_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE6 n = Branch3.netE6 n := by
  unfold Branch6Encoder.netE6 Branch3.netE6; rw [netE5_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE7_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE7 n = Branch3.netE7 n := by
  unfold Branch6Encoder.netE7 Branch3.netE7; rw [netE6_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE8_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE8 n = Branch3.netE8 n := by
  unfold Branch6Encoder.netE8 Branch3.netE8; rw [netE7_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE9_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE9 n = Branch3.netE9 n := by
  unfold Branch6Encoder.netE9 Branch3.netE9; rw [netE8_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE10_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE10 n = Branch3.netE10 n := by
  unfold Branch6Encoder.netE10 Branch3.netE10; rw [netE9_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE11_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE11 n = Branch3.netE11 n := by
  unfold Branch6Encoder.netE11 Branch3.netE11; rw [netE10_b6_eq_b3, paramJ_b6_eq_b3, paramL_b6_eq_b3]
lemma netE12_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE12 n = Branch3.netE12 n := by
  unfold Branch6Encoder.netE12 Branch3.netE12; rw [netE11_b6_eq_b3]
lemma netE13_b6_eq_b3 (n : ℕ) : Branch6Encoder.netE13 n = Branch3.netE13 n := by
  unfold Branch6Encoder.netE13 Branch3.netE13
  rw [netE12_b6_eq_b3, treeLog_b6_eq_b3, treeEdgeOff_b6_eq_b3]
lemma netEdgeCount_b6_eq_b3 (n : ℕ) : Branch6Encoder.netEdgeCount n = Branch3.netEdgeCount n := by
  unfold Branch6Encoder.netEdgeCount Branch3.netEdgeCount
  rw [netE13_b6_eq_b3, treeLog_b6_eq_b3]

lemma ovlTargetBit_b6_eq_b3 (J blk p : ℕ) :
    Branch6Encoder.ovlTargetBit J blk p = Branch3.ovlTargetBit J blk p := rfl

lemma endsB0_b6_eq_b3 (n e : ℕ) : Branch6Encoder.endsB0 n e = Branch3.endsB0 n e := rfl
lemma endsB1_b6_eq_b3 (n i : ℕ) : Branch6Encoder.endsB1 n i = Branch3.endsB1 n i := by
  unfold Branch6Encoder.endsB1 Branch3.endsB1
  rw [netV1_b6_eq_b3, netV12_b6_eq_b3, netV5_b6_eq_b3, paramJ_b6_eq_b3, paramL2_b6_eq_b3]
lemma endsB2_b6_eq_b3 (n leaf : ℕ) : Branch6Encoder.endsB2 n leaf = Branch3.endsB2 n leaf := by
  unfold Branch6Encoder.endsB2 Branch3.endsB2
  rw [treeM_b6_eq_b3, netV1_b6_eq_b3, netV13_b6_eq_b3, netV14_b6_eq_b3, netV15_b6_eq_b3]
lemma endsB3_b6_eq_b3 (n idx : ℕ) : Branch6Encoder.endsB3 n idx = Branch3.endsB3 n idx := by
  unfold Branch6Encoder.endsB3 Branch3.endsB3
  rw [netV2_b6_eq_b3, netV3_b6_eq_b3, paramJ_b6_eq_b3, paramL2_b6_eq_b3]
lemma endsB4_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB4 n k = Branch3.endsB4 n k := by
  unfold Branch6Encoder.endsB4 Branch3.endsB4
  rw [paramJ_b6_eq_b3, netV3_b6_eq_b3, netV4_b6_eq_b3, paramL1_b6_eq_b3]
lemma endsB5_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB5 n k = Branch3.endsB5 n k := by
  unfold Branch6Encoder.endsB5 Branch3.endsB5
  rw [paramJ_b6_eq_b3, netV4_b6_eq_b3, netV7_b6_eq_b3, paramL1_b6_eq_b3]
lemma endsB6_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB6 n k = Branch3.endsB6 n k := by
  unfold Branch6Encoder.endsB6 Branch3.endsB6
  rw [paramJ_b6_eq_b3, netV5_b6_eq_b3, netV6_b6_eq_b3, paramL1_b6_eq_b3]
lemma endsB7_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB7 n k = Branch3.endsB7 n k := by
  unfold Branch6Encoder.endsB7 Branch3.endsB7
  rw [paramJ_b6_eq_b3, netV6_b6_eq_b3, netV7_b6_eq_b3, paramL1_b6_eq_b3]
lemma endsB8_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB8 n k = Branch3.endsB8 n k := by
  unfold Branch6Encoder.endsB8 Branch3.endsB8
  rw [paramJ_b6_eq_b3, netV7_b6_eq_b3, netV8_b6_eq_b3, paramL2_b6_eq_b3]
lemma endsB9_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB9 n k = Branch3.endsB9 n k := by
  unfold Branch6Encoder.endsB9 Branch3.endsB9
  rw [paramJ_b6_eq_b3, netV8_b6_eq_b3, netV9_b6_eq_b3, paramL1_b6_eq_b3]
lemma endsB10_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB10 n k = Branch3.endsB10 n k := by
  unfold Branch6Encoder.endsB10 Branch3.endsB10
  dsimp only
  rw [paramJ_b6_eq_b3, ovlTargetBit_b6_eq_b3, netV9_b6_eq_b3, paramL1_b6_eq_b3,
      netV11_b6_eq_b3, netV10_b6_eq_b3]
lemma endsB11_b6_eq_b3 (n k : ℕ) : Branch6Encoder.endsB11 n k = Branch3.endsB11 n k := by
  unfold Branch6Encoder.endsB11 Branch3.endsB11
  rw [netV11_b6_eq_b3, netV12_b6_eq_b3]
lemma endsB12_b6_eq_b3 (n locE : ℕ) : Branch6Encoder.endsB12 n locE = Branch3.endsB12 n locE := by
  unfold Branch6Encoder.endsB12 Branch3.endsB12
  dsimp only
  simp only [treeLog_b6_eq_b3, decodeTreeEdge_b6_eq_b3, netV15_b6_eq_b3, netV17_b6_eq_b3,
      treeVertOff_b6_eq_b3]
lemma endsB13_b6_eq_b3 (n b : ℕ) : Branch6Encoder.endsB13 n b = Branch3.endsB13 n b := by
  unfold Branch6Encoder.endsB13 Branch3.endsB13
  dsimp only
  rw [treeLog_b6_eq_b3, netV16_b6_eq_b3, netV17_b6_eq_b3, netV18_b6_eq_b3]

theorem rawEnds_b6_eq_b3 (n e : ℕ) : Branch6Encoder.rawEnds n e = Branch3.rawEnds n e := by
  unfold Branch6Encoder.rawEnds Branch3.rawEnds
  rw [netE1_b6_eq_b3, netE2_b6_eq_b3, netE3_b6_eq_b3, netE4_b6_eq_b3, netE5_b6_eq_b3,
      netE6_b6_eq_b3, netE7_b6_eq_b3, netE8_b6_eq_b3, netE9_b6_eq_b3, netE10_b6_eq_b3,
      netE11_b6_eq_b3, netE12_b6_eq_b3, netE13_b6_eq_b3,
      endsB0_b6_eq_b3, endsB1_b6_eq_b3, endsB2_b6_eq_b3, endsB3_b6_eq_b3, endsB4_b6_eq_b3,
      endsB5_b6_eq_b3, endsB6_b6_eq_b3, endsB7_b6_eq_b3, endsB8_b6_eq_b3, endsB9_b6_eq_b3,
      endsB10_b6_eq_b3, endsB11_b6_eq_b3, endsB12_b6_eq_b3, endsB13_b6_eq_b3]

lemma netV10_b8_eq_b3 (n : ℕ) : Branch8CircuitEmit.netV10 n = Branch3.netV10 n :=
  netV10_b6_eq_b3 n

lemma rawPred_b8_eq_b3 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    {v : ℕ} (hv : v < Branch3.netV10 n) :
    Branch8CircuitEmit.rawPred mode n h s t0 t1 pre v =
      Branch3.rawPred mode n h s t0 t1 pre v := by
  unfold Branch8CircuitEmit.rawPred Branch3.rawPred
  dsimp only
  have hV1 : Branch8CircuitEmit.netV1 n = Branch3.netV1 n := netV1_b6_eq_b3 n
  have hV2 : Branch8CircuitEmit.netV2 n = Branch3.netV2 n := netV2_b6_eq_b3 n
  have hV3 : Branch8CircuitEmit.netV3 n = Branch3.netV3 n := netV3_b6_eq_b3 n
  have hV4 : Branch8CircuitEmit.netV4 n = Branch3.netV4 n := netV4_b6_eq_b3 n
  have hV5 : Branch8CircuitEmit.netV5 n = Branch3.netV5 n := netV5_b6_eq_b3 n
  have hV6 : Branch8CircuitEmit.netV6 n = Branch3.netV6 n := netV6_b6_eq_b3 n
  have hV7 : Branch8CircuitEmit.netV7 n = Branch3.netV7 n := netV7_b6_eq_b3 n
  have hV8 : Branch8CircuitEmit.netV8 n = Branch3.netV8 n := netV8_b6_eq_b3 n
  have hV9 : Branch8CircuitEmit.netV9 n = Branch3.netV9 n := netV9_b6_eq_b3 n
  have hV10 : Branch8CircuitEmit.netV10 n = Branch3.netV10 n := netV10_b6_eq_b3 n
  have hJ : Branch8CircuitEmit.paramJ n = Branch3.paramJ n := paramJ_b6_eq_b3 n
  have hL1 : Branch8CircuitEmit.paramL1 n = Branch3.paramL1 n := paramL1_b6_eq_b3 n
  have hL2 : Branch8CircuitEmit.paramL2 n = Branch3.paramL2 n := paramL2_b6_eq_b3 n
  have hOm : Branch8CircuitEmit.paramOmegaExp n = Branch3.paramOmegaExp n := paramOmegaExp_b6_eq_b3 n
  have hIOm : Branch8CircuitEmit.paramInvOmegaExp n = Branch3.paramInvOmegaExp n := paramInvOmegaExp_b6_eq_b3 n
  rw [hV1, hV2, hV3, hV4, hV5, hV6, hV7, hV8, hV9, hV10, hJ, hL1, hL2, hOm, hIOm]
  have hf1 : Branch8CircuitEmit.fwdSt1InIndices = Branch3.fwdSt1InIndices := rfl
  have hf2 : Branch8CircuitEmit.fwdSt1Mat = Branch3.fwdSt1Mat := rfl
  have hf3 : Branch8CircuitEmit.st2Mat = Branch3.st2Mat := rfl
  have hf4 : Branch8CircuitEmit.ringMulTensor = Branch3.ringMulTensor := rfl
  have hf5 : Branch8CircuitEmit.fullSt1Mat = Branch3.fullSt1Mat := rfl
  have hz : Branch8CircuitEmit.zmod2ToBool = Branch3.zmod2ToBool := rfl
  rw [hf1, hf2, hf3, hf4, hf5, hz]
  by_cases h1 : v < Branch3.netV1 n
  · simp only [h1, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
  simp only [h1, ↓reduceIte]
  by_cases h2 : v < Branch3.netV2 n
  · simp only [h2, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h2, ↓reduceIte]
  by_cases h3 : v < Branch3.netV3 n
  · simp only [h3, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
  simp only [h3, ↓reduceIte]
  by_cases h4 : v < Branch3.netV4 n
  · simp only [h4, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h4, ↓reduceIte]
  by_cases h5 : v < Branch3.netV5 n
  · simp only [h5, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h5, ↓reduceIte]
  by_cases h6 : v < Branch3.netV6 n
  · simp only [h6, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h6, ↓reduceIte]
  by_cases h7 : v < Branch3.netV7 n
  · simp only [h7, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h7, ↓reduceIte]
  by_cases h8 : v < Branch3.netV8 n
  · simp only [h8, ↓reduceIte]; exact (GlueNetConv.branch3_bilinearMapCheckCircuit_eq _ _ _ _).symm
  simp only [h8, ↓reduceIte]
  by_cases h9 : v < Branch3.netV9 n
  · simp only [h9, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h9, hv, ↓reduceIte]
  exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm

lemma rawPredTail_b8b_eq_b3 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    {v : ℕ} (hv : Branch3.netV10 n ≤ v) :
    Branch8bTail.rawPredTail mode n s t0 t1 v =
      Branch3.rawPred mode n h s t0 t1 pre v := by
  rcases Branch3.netV_chain n with
    ⟨_, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, _, _, _, _, _, _, _, _, _⟩
  unfold Branch8bTail.rawPredTail Branch3.rawPred
  dsimp only
  have hlt1 : ¬(v < Branch3.netV1 n) := by omega
  have hlt2 : ¬(v < Branch3.netV2 n) := by omega
  have hlt3 : ¬(v < Branch3.netV3 n) := by omega
  have hlt4 : ¬(v < Branch3.netV4 n) := by omega
  have hlt5 : ¬(v < Branch3.netV5 n) := by omega
  have hlt6 : ¬(v < Branch3.netV6 n) := by omega
  have hlt7 : ¬(v < Branch3.netV7 n) := by omega
  have hlt8 : ¬(v < Branch3.netV8 n) := by omega
  have hlt9 : ¬(v < Branch3.netV9 n) := by omega
  have hlt10 : ¬(v < Branch3.netV10 n) := by omega
  simp only [hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, ↓reduceIte]
  rw [paramJ_b6_eq_b3, paramL_b6_eq_b3, treeLog_b6_eq_b3,
      netV10_b6_eq_b3, netV11_b6_eq_b3, netV12_b6_eq_b3, netV13_b6_eq_b3,
      netV14_b6_eq_b3, netV15_b6_eq_b3, netV16_b6_eq_b3, netV17_b6_eq_b3, netV18_b6_eq_b3,
      decodeTreeVert_b8b_eq_b3]
  have hovl : Branch8bTail.ovlInLocal = Branch3.ovlInLocal := rfl
  have hz : Branch8bTail.zmod2ToBool = Branch3.zmod2ToBool := rfl
  have hotb : Branch6Encoder.ovlTargetBit = Branch3.ovlTargetBit := rfl
  rw [hovl, hz, hotb]
  by_cases h11 : v < Branch3.netV11 n
  · simp only [h11, ↓reduceIte]; exact (GlueNetConv.branch3_constCircuit_eq _ _).symm
  simp only [h11, ↓reduceIte]
  by_cases h12 : v < Branch3.netV12 n
  · simp only [h12, ↓reduceIte]; exact (GlueNetConv.branch3_linearMapCheckCircuit_eq _ _ _).symm
  simp only [h12, ↓reduceIte]
  by_cases h13 : v < Branch3.netV13 n
  · simp only [h13, ↓reduceIte]; exact (GlueNetConv.branch3_synCheckCircuit_eq _).symm
  simp only [h13, ↓reduceIte]
  by_cases h14 : v < Branch3.netV14 n
  · simp only [h14, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
  simp only [h14, ↓reduceIte]
  by_cases h15 : v < Branch3.netV15 n
  · simp only [h15, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
  simp only [h15, ↓reduceIte]
  by_cases h16 : v < Branch3.netV16 n
  · simp only [h16, ↓reduceIte]
    by_cases hu : (Branch3.decodeTreeVert (Branch3.treeLog n + 1) (v - Branch3.netV15 n)).2.2 = 0
    · simp only [hu, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
    simp only [hu, ↓reduceIte]
    by_cases hm2 : mode = 2 ∧ (Branch3.decodeTreeVert (Branch3.treeLog n + 1) (v - Branch3.netV15 n)).1 = Branch3.treeLog n + 1
    · simp only [hm2]; exact (GlueNetConv.branch3_sepFullAdderCircuit_eq _ _ _).symm
    simp only [hm2, ↓reduceIte]; exact GlueNetConv.branch3_fullAdderCircuit_eq.symm
  simp only [h16, ↓reduceIte]
  by_cases h17 : v < Branch3.netV17 n
  · simp only [h17, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm
  simp only [h17, ↓reduceIte]
  by_cases h18 : v < Branch3.netV18 n
  · simp only [h18, ↓reduceIte]
    by_cases hm0 : mode = 0
    · simp only [hm0, ↓reduceIte]; exact (GlueNetConv.branch3_exactCmpStepCircuit_eq _ _).symm
    simp only [hm0, ↓reduceIte]
    by_cases hm1 : mode = 1
    · simp only [hm1, ↓reduceIte]; exact (GlueNetConv.branch3_borrowStepCircuit_eq _).symm
    simp only [hm1, ↓reduceIte]; exact GlueNetConv.branch3_sepCmpStepCircuit_eq.symm
  simp only [h18, ↓reduceIte]
  by_cases hm1 : mode = 1 ∧ ¬t0 < 2 ^ (Branch3.treeLog n + 2)
  · simp only [hm1]; exact (GlueNetConv.branch3_constCircuit_eq _ _).symm
  simp only [hm1, ↓reduceIte]; exact (GlueNetConv.branch3_pinBitCircuit_eq _).symm

/-- Exact vertex-circuit stream split bridging `Branch3.rawPred` to
`Branch8CircuitEmit.rawPred` (Blocks 0–9) followed by `Branch8bTail.rawPredTail` (Blocks 10–18). -/
theorem circuits_flatMap_split_eq (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    (List.range (Branch3.netVertCount n)).flatMap
      (fun v => QCSD_encodeCircuit (Branch3.rawPred mode n h s t0 t1 pre v)) =
    (List.range (Branch8CircuitEmit.netV10 n)).flatMap
      (fun v => QCSD_encodeCircuit (Branch8CircuitEmit.rawPred mode n h s t0 t1 pre v)) ++
    (List.range (Branch6Encoder.netVertCount n - Branch6Encoder.netV10 n)).flatMap
      (fun d => QCSD_encodeCircuit (Branch8bTail.rawPredTail mode n s t0 t1 (Branch6Encoder.netV10 n + d))) := by
  have hle : Branch3.netV10 n ≤ Branch3.netVertCount n := by
    rcases Branch3.netV_chain n with
      ⟨_, _, _, _, _, _, _, _, _, _, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    omega
  have hsum : Branch3.netVertCount n = Branch3.netV10 n + (Branch3.netVertCount n - Branch3.netV10 n) := by
    omega
  conv_lhs => rw [hsum, List.range_add, List.flatMap_append, List.flatMap_map]
  rw [netV10_b8_eq_b3, netVertCount_b6_eq_b3, netV10_b6_eq_b3]
  congr 1
  · apply List.flatMap_congr
    intro v hv
    rw [rawPred_b8_eq_b3 mode n h s t0 t1 pre (List.mem_range.mp hv)]
  · apply List.flatMap_congr
    intro d _
    rw [rawPredTail_b8b_eq_b3 mode n h s t0 t1 pre (Nat.le_add_right _ _)]

/-- Canonical middle output stream emitted by the `M_net` register machine (before `Branch4_TMCompiler`
prepends `List.replicate W true` and appends the `W` isolated padding circuits). -/
def mnetMiddleStream (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) : List Bool :=
  List.replicate (Branch3.netVertCount n) true ++ [false] ++
  QCSD_natToUnary (Branch3.netEdgeCount n) ++
  (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
    QCSD_natToUnary (Branch3.rawEnds n e).1 ++ QCSD_natToUnary (Branch3.rawEnds n e).2) ++
  (List.range (Branch3.netVertCount n)).flatMap (fun v =>
    QCSD_encodeCircuit (Branch3.rawPred mode n h s t0 t1 pre v))

theorem mnet_concat_eq_middleStream (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) :
    (QCSD_natToUnary (Branch6Encoder.netVertCount n) ++ QCSD_natToUnary (Branch6Encoder.netEdgeCount n)) ++
    (List.range (Branch6Encoder.netEdgeCount n)).flatMap (fun e =>
      QCSD_natToUnary (Branch6Encoder.rawEnds n e).1 ++ QCSD_natToUnary (Branch6Encoder.rawEnds n e).2) ++
    ((List.range (Branch8CircuitEmit.netV10 n)).flatMap
      (fun v => QCSD_encodeCircuit (Branch8CircuitEmit.rawPred mode n h s t0 t1 pre v)) ++
     (List.range (Branch6Encoder.netVertCount n - Branch6Encoder.netV10 n)).flatMap
      (fun d => QCSD_encodeCircuit (Branch8bTail.rawPredTail mode n s t0 t1 (Branch6Encoder.netV10 n + d)))) =
    mnetMiddleStream mode n h s t0 t1 pre := by
  rw [← circuits_flatMap_split_eq mode n h s t0 t1 pre,
      netVertCount_b6_eq_b3, netEdgeCount_b6_eq_b3]
  have hedges :
      (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
        QCSD_natToUnary (Branch6Encoder.rawEnds n e).1 ++ QCSD_natToUnary (Branch6Encoder.rawEnds n e).2) =
      (List.range (Branch3.netEdgeCount n)).flatMap (fun e =>
        QCSD_natToUnary (Branch3.rawEnds n e).1 ++ QCSD_natToUnary (Branch3.rawEnds n e).2) := by
    apply List.flatMap_congr
    intro e _
    rw [rawEnds_b6_eq_b3]
  rw [hedges]
  unfold mnetMiddleStream QCSD_natToUnary
  simp only [List.append_assoc]

theorem encodeNet2_padNet_N_exact_eq_mnetWrap (W : ℕ) (x : QCSD_Instance) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_exact x pre)) =
      List.replicate W true ++
      (mnetMiddleStream 0 x.n x.h x.s x.t 0 pre ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) := by
  rw [GlueNetConv.encodeNet2_padNet_N_exact_stream_split_exact W x pre]
  unfold mnetMiddleStream
  simp only [List.append_assoc]

theorem encodeNet2_padNet_N_le_eq_mnetWrap (W : ℕ) (x : QCSD_Instance) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_le x pre)) =
      List.replicate W true ++
      (mnetMiddleStream 1 x.n x.h x.s x.t 0 pre ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) := by
  rw [GlueNetConv.encodeNet2_padNet_N_le_stream_split_exact W x pre]
  unfold mnetMiddleStream
  simp only [List.append_assoc]

theorem encodeNet2_padNet_N_sep_eq_mnetWrap (W : ℕ) (x : QCSD_InstanceSep) (pre : List Bool) :
    QCSD_encodeNet2 (padNet W (Branch3.N_sep x pre)) =
      List.replicate W true ++
      (mnetMiddleStream 2 x.n x.h x.s x.t₀ x.t₁ pre ++
       (List.range W).flatMap (fun _ => [false, true, false, false, false, true])) := by
  rw [GlueNetConv.encodeNet2_padNet_N_sep_stream_split_exact W x pre]
  unfold mnetMiddleStream
  simp only [List.append_assoc]

/-!
# Section 2: General `RMExec` Emission Bound, Unified Register Bank (`R_mnet = 98`), and Glue Sub-Programs
-/

lemma rmStep_emitted_length_le_one {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool)
    {q q' : Q} {reg reg' : RegState R} {b : List Bool}
    (hstep : rmStep M inp q reg = some (q', reg', b)) : b.length ≤ 1 := by
  unfold rmStep at hstep
  cases hM : M q with
  | none => rw [hM] at hstep; cases hstep
  | some op =>
    rw [hM] at hstep
    rcases op with ⟨r, next⟩ | ⟨r, next⟩ | ⟨r, qz, qnz⟩ | ⟨d, s, next⟩ | ⟨r, qf, qt⟩ | ⟨bit, next⟩
    · dsimp only at hstep; cases hstep; decide
    · dsimp only at hstep; cases hstep; decide
    · dsimp only at hstep; split_ifs at hstep <;> cases hstep <;> decide
    · dsimp only at hstep; cases hstep; decide
    · dsimp only at hstep; split_ifs at hstep <;> cases hstep <;> decide
    · dsimp only at hstep; cases hstep; simp

lemma rmIter_emitted_length_le {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool) :
    ∀ (k : ℕ) (q₀ q₁ : Q) (reg₀ reg₁ : RegState R) (out : List Bool),
      rmIter M inp k q₀ reg₀ = some (q₁, reg₁, out) → out.length ≤ k
  | 0, _, _, _, _, _, h => by cases h; decide
  | k + 1, q₀, q₁, reg₀, reg₁, out, h => by
    simp only [rmIter] at h
    cases hs : rmStep M inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', b⟩
      simp only [hs] at h
      cases hr : rmIter M inp k q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h
        cases h
        have hb := rmStep_emitted_length_le_one M inp hs
        have ho := rmIter_emitted_length_le M inp k q' q₁ reg' reg₁ out' hr
        rw [List.length_append]
        omega

/-- Every `RMExec` emits at most 1 bit per step (`emitted.length ≤ steps`). -/
theorem rmExec_emitted_length_le {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M V inp q₀ reg₀ q₁ reg₁ out T) : out.length ≤ T := by
  rcases h with ⟨k, hk, hiter, _, _⟩
  exact le_trans (rmIter_emitted_length_le M inp k q₀ q₁ reg₀ reg₁ out hiter) hk

/-- Unified 98-register bank: `0..55` = `EncR` (`Branch6b`/`Branch8b`), `56..97` = `R_emit` (`Branch8`). -/
abbrev R_mnet : ℕ := EncR + Branch8CircuitEmit.R_emit

def embEnc (r : Fin EncR) : Fin R_mnet :=
  ⟨r.val, by have := r.isLt; dsimp only [R_mnet, EncR, Branch8CircuitEmit.R_emit] at *; omega⟩
def embEmit (r : Fin Branch8CircuitEmit.R_emit) : Fin R_mnet :=
  ⟨EncR + r.val, by have := r.isLt; dsimp only [R_mnet, EncR, Branch8CircuitEmit.R_emit] at *; omega⟩

lemma embEnc_injective : Function.Injective embEnc := by
  intro a b h
  have hv : a.val = b.val := congrArg (Fin.val : Fin R_mnet → ℕ) h
  exact Fin.ext hv

lemma embEmit_injective : Function.Injective embEmit := by
  intro a b h
  have hv : EncR + a.val = EncR + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

lemma embEnc_ne_embEmit (a : Fin EncR) (b : Fin Branch8CircuitEmit.R_emit) :
    embEnc a ≠ embEmit b := by
  intro h
  have hv : a.val = EncR + b.val := congrArg Fin.val h
  have ha := a.isLt
  omega

lemma not_embEnc_iff (i : Fin R_mnet) :
    (∀ j : Fin EncR, embEnc j ≠ i) ↔ EncR ≤ i.val := by
  constructor
  · intro h
    by_contra hlt
    exact h ⟨i.val, by omega⟩ (Fin.ext rfl)
  · intro hge j heq
    have hv : j.val = i.val := congrArg Fin.val heq
    have hj := j.isLt
    omega

lemma not_embEmit_iff (i : Fin R_mnet) :
    (∀ j : Fin Branch8CircuitEmit.R_emit, embEmit j ≠ i) ↔ i.val < EncR := by
  constructor
  · intro h
    by_contra hge
    have hi := i.isLt
    exact h ⟨i.val - EncR, by dsimp only [R_mnet, EncR, Branch8CircuitEmit.R_emit] at *; omega⟩
      (Fin.ext (by dsimp only [embEmit]; omega))
  · intro hlt j heq
    have hv : EncR + j.val = i.val := congrArg Fin.val heq
    omega

/-! ### Stage 3 Sub-Program: `rmEmitNetHeader` (`QCSD_natToUnary netVertCount ++ QCSD_natToUnary netEdgeCount`) -/

abbrev RMEmitNetHeaderQ : Type := RMEmitUnaryQ ⊕ RMEmitUnaryQ

def rmEmitNetHeader : RMProg EncR RMEmitNetHeaderQ :=
  rmChain (rmEmitUnary regVertCount regS0) (rmEmitUnary regEdgeCount regS0) rmEmitUnaryEntry

def rmEmitNetHeaderEntry : RMEmitNetHeaderQ := Sum.inl rmEmitUnaryEntry
def rmEmitNetHeaderExit : RMEmitNetHeaderQ := Sum.inr rmEmitUnaryExit

theorem rmEmitNetHeader_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ i, reg₀ i ≤ V) :
    ∃ reg₁ : RegState EncR,
      ParamsLoaded n reg₁ ∧
      (∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec rmEmitNetHeader V inp rmEmitNetHeaderEntry reg₀ rmEmitNetHeaderExit reg₁
        (QCSD_natToUnary (Branch6Encoder.netVertCount n) ++
         QCSD_natToUnary (Branch6Encoder.netEdgeCount n))
        (2 * Branch6Encoder.netVertCount n + 2 * Branch6Encoder.netEdgeCount n + 6) := by
  have hvc : reg₀ regVertCount = Branch6Encoder.netVertCount n := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hec : reg₀ regEdgeCount = Branch6Encoder.netEdgeCount n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e1 := rmEmitUnary_spec regVertCount regS0 (by decide) V inp reg₀ hreg₀
  set r1 := regUpd reg₀ regS0 0
  have h1_ec : r1 regEdgeCount = reg₀ regEdgeCount := regUpd_ne reg₀ (by decide) 0
  have e2 := rmEmitUnary_spec regEdgeCount regS0 (by decide) V inp r1 e1.reg₁_le
  have hact : rmEmitUnary regVertCount regS0 rmEmitUnaryEntry ≠ none := by
    simp [rmEmitUnary, rmEmitUnaryEntry, rmEmitTrueRepeat, rmEmitTrueRepeatEntry,
      rmChain, rmSeq, rmCopy]
  have hcomb := rmChain_spec_inl hact e1 e2
  rw [hvc, h1_ec, hec, max_self] at hcomb
  set r2 := regUpd r1 regS0 0
  have hpr : Branch6Encoder.PreservedRegs r2 reg₀ := by
    intro i hi
    dsimp only [r2, r1]
    have hne : i ≠ regS0 := fun h => by subst h; simp at hi
    rw [regUpd_ne _ hne, regUpd_ne _ hne]
  have hT : 2 * Branch6Encoder.netVertCount n + 3 + (2 * Branch6Encoder.netEdgeCount n + 3) =
      2 * Branch6Encoder.netVertCount n + 2 * Branch6Encoder.netEdgeCount n + 6 := by ring
  rw [hT] at hcomb
  exact ⟨r2, hp.of_preserved hpr, fun i _ hi2 => hpr i (by omega), hcomb⟩

/-! ### Stage 5 Sub-Program: `rmCopyTier0ToEmit` (copies 15 Tier-0 registers from `0..55` to `56..70`) -/

def tier0Pairs : Fin 15 → Fin Branch8CircuitEmit.R_emit × Fin EncR
  | ⟨0, _⟩  => (Branch8CircuitEmit.rN,       regN)
  | ⟨1, _⟩  => (Branch8CircuitEmit.rHOff,    regOffH)
  | ⟨2, _⟩  => (Branch8CircuitEmit.rSOff,    regOffS)
  | ⟨3, _⟩  => (Branch8CircuitEmit.rPreOff,  regOffPre)
  | ⟨4, _⟩  => (Branch8CircuitEmit.rPreLen,  regPreLen)
  | ⟨5, _⟩  => (Branch8CircuitEmit.rT0,      regT0)
  | ⟨6, _⟩  => (Branch8CircuitEmit.rT1,      regT1)
  | ⟨7, _⟩  => (Branch8CircuitEmit.rJ,       regJ)
  | ⟨8, _⟩  => (Branch8CircuitEmit.rL,       regL)
  | ⟨9, _⟩  => (Branch8CircuitEmit.rL1,      regL1)
  | ⟨10, _⟩ => (Branch8CircuitEmit.rL2,      regL2)
  | ⟨11, _⟩ => (Branch8CircuitEmit.rWExp,    regOmega)
  | ⟨12, _⟩ => (Branch8CircuitEmit.rInvWExp, regInvOmega)
  | ⟨13, _⟩ => (Branch8CircuitEmit.rTreeLog, regTreeLog)
  | ⟨14, _⟩ => (Branch8CircuitEmit.rTreeM,   regTreeM)

lemma tier0Pairs_fst_val (k : Fin 15) : (tier0Pairs k).1.val = k.val := by
  fin_cases k <;> rfl

def rmCopyTier0ToEmit : RMProg R_mnet (Fin 16) :=
  fun q =>
    if h : q.val < 15 then
      let p := tier0Pairs ⟨q.val, h⟩
      some (opCopy (embEmit p.1) (embEnc p.2) ⟨q.val + 1, by omega⟩)
    else none

def rmCopyTier0ToEmitEntry : Fin 16 := 0
def rmCopyTier0ToEmitExit : Fin 16 := ⟨15, by decide⟩

lemma rmCopyTier0ToEmit_aux (V : ℕ) (inp : List Bool) :
    ∀ (rem i : ℕ) (hi : i + rem = 15) (reg : RegState R_mnet),
      (∀ r, reg r ≤ V) →
      ∃ reg₁ : RegState R_mnet,
        (∀ j : Fin EncR, reg₁ (embEnc j) = reg (embEnc j)) ∧
        (∀ (k : Fin 15), i ≤ k.val → reg₁ (embEmit (tier0Pairs k).1) = reg (embEnc (tier0Pairs k).2)) ∧
        (∀ (k : Fin 15), k.val < i → reg₁ (embEmit (tier0Pairs k).1) = reg (embEmit (tier0Pairs k).1)) ∧
        (∀ (k : Fin Branch8CircuitEmit.R_emit), 15 ≤ k.val → reg₁ (embEmit k) = reg (embEmit k)) ∧
        RMExec rmCopyTier0ToEmit V inp ⟨i, by omega⟩ reg rmCopyTier0ToEmitExit reg₁ [] rem
  | 0, i, hi, reg, hreg => by
    obtain rfl : i = 15 := by omega
    refine ⟨reg, fun _ => rfl, fun k hk => by omega, fun _ _ => rfl, fun _ _ => rfl,
      0, Nat.le_refl 0, by rfl, by simp [rmCopyTier0ToEmit, rmCopyTier0ToEmitExit], ?_⟩
    intro j hj q' reg' out' hji
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    cases hji; exact hreg
  | rem + 1, i, hi, reg, hreg => by
    have hilt : i < 15 := by omega
    set p := tier0Pairs ⟨i, hilt⟩
    set reg' := regUpd reg (embEmit p.1) (reg (embEnc p.2))
    have hstep : rmStep rmCopyTier0ToEmit inp ⟨i, by omega⟩ reg =
        some (⟨i + 1, by omega⟩, reg', []) := by
      simp [rmStep, rmCopyTier0ToEmit, opCopy, hilt, p, reg']
    have hreg'_le : ∀ r, reg' r ≤ V := regUpd_le hreg _ (hreg _)
    rcases rmCopyTier0ToEmit_aux V inp rem (i + 1) (by omega) reg' hreg'_le
      with ⟨reg₁, hEnc, hGe, hLt, hHi, k, hk, hiter, hhalt, hbnd⟩
    have hreg'_enc : ∀ j : Fin EncR, reg' (embEnc j) = reg (embEnc j) := fun j =>
      regUpd_ne reg (embEnc_ne_embEmit j p.1) _
    refine ⟨reg₁,
      fun j => (hEnc j).trans (hreg'_enc j),
      fun m hm => ?_,
      fun m hm => ?_,
      fun m hm => ?_,
      k + 1, by omega, ?_, hhalt, ?_⟩
    · rcases Nat.eq_or_lt_of_le hm with heq | hgt
      · have hmk : m = ⟨i, hilt⟩ := Fin.ext heq.symm
        subst hmk
        have h1 := hLt ⟨i, hilt⟩ (by omega)
        dsimp only [p, reg'] at h1 ⊢
        rw [h1, regUpd_self]
      · exact (hGe m (by omega)).trans (hreg'_enc (tier0Pairs m).2)
    · have hne : embEmit (tier0Pairs m).1 ≠ embEmit p.1 := by
        intro heq
        have hv := congrArg Fin.val (embEmit_injective heq)
        dsimp only [p] at hv
        rw [tier0Pairs_fst_val, tier0Pairs_fst_val] at hv
        dsimp only at hv
        omega
      exact (hLt m (by omega)).trans (regUpd_ne reg hne _)
    · have hne : embEmit m ≠ embEmit p.1 := by
        intro heq
        have hv := congrArg Fin.val (embEmit_injective heq)
        dsimp only [p] at hv
        rw [tier0Pairs_fst_val] at hv
        dsimp only at hv
        omega
      exact (hHi m hm).trans (regUpd_ne reg hne _)
    · conv => lhs; unfold rmIter
      simp only [hstep, hiter, List.nil_append]
    · intro j hj q' r' out' hji
      cases j with
      | zero => cases hji; exact hreg
      | succ j' =>
        conv at hji => lhs; unfold rmIter
        simp only [hstep] at hji
        cases hr : rmIter rmCopyTier0ToEmit inp j' ⟨i + 1, by omega⟩ reg' with
        | none => simp only [hr] at hji; cases hji
        | some val =>
          rcases val with ⟨q'', r'', out''⟩
          simp only [hr] at hji; cases hji
          exact hbnd j' (by omega) q' r' out'' hr

theorem rmCopyTier0ToEmit_spec (n V : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (reg₀ : RegState R_mnet)
    (hreg₀ : ∀ r, reg₀ r ≤ V)
    (hp : ParamsLoaded n (fun j => reg₀ (embEnc j)))
    (hT0 : reg₀ (embEnc regT0) = t0)
    (hT1 : reg₀ (embEnc regT1) = t1)
    (hPL : reg₀ (embEnc regPreLen) = pre.length)
    (hh_bits : ∀ (i : ℕ) (hi : i < n),
      inp.getD (reg₀ (embEnc regOffH) + i) false = decide (h ⟨i, hi⟩ = (1 : ZMod 2)))
    (hs_bits : ∀ (i : ℕ) (hi : i < n),
      inp.getD (reg₀ (embEnc regOffS) + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2)))
    (hpre_bits : ∀ i < pre.length,
      inp.getD (reg₀ (embEnc regOffPre) + i) false = pre.getD i false) :
    ∃ reg₁ : RegState R_mnet,
      (∀ j : Fin EncR, reg₁ (embEnc j) = reg₀ (embEnc j)) ∧
      Branch8CircuitEmit.ValidTier0 n h s t0 t1 pre inp (fun j => reg₁ (embEmit j)) ∧
      RMExec rmCopyTier0ToEmit V inp rmCopyTier0ToEmitEntry reg₀ rmCopyTier0ToEmitExit reg₁ [] 15 := by
  rcases rmCopyTier0ToEmit_aux V inp 15 0 rfl reg₀ hreg₀ with ⟨reg₁, hEnc, hGe, _, _, hex⟩
  refine ⟨reg₁, hEnc, ?_, hex⟩
  have h0  := hGe ⟨0, by decide⟩ (Nat.zero_le _)
  have h1  := hGe ⟨1, by decide⟩ (Nat.zero_le _)
  have h2  := hGe ⟨2, by decide⟩ (Nat.zero_le _)
  have h3  := hGe ⟨3, by decide⟩ (Nat.zero_le _)
  have h4  := hGe ⟨4, by decide⟩ (Nat.zero_le _)
  have h5  := hGe ⟨5, by decide⟩ (Nat.zero_le _)
  have h6  := hGe ⟨6, by decide⟩ (Nat.zero_le _)
  have h7  := hGe ⟨7, by decide⟩ (Nat.zero_le _)
  have h8  := hGe ⟨8, by decide⟩ (Nat.zero_le _)
  have h9  := hGe ⟨9, by decide⟩ (Nat.zero_le _)
  have h10 := hGe ⟨10, by decide⟩ (Nat.zero_le _)
  have h11 := hGe ⟨11, by decide⟩ (Nat.zero_le _)
  have h12 := hGe ⟨12, by decide⟩ (Nat.zero_le _)
  have h13 := hGe ⟨13, by decide⟩ (Nat.zero_le _)
  have h14 := hGe ⟨14, by decide⟩ (Nat.zero_le _)
  dsimp only [tier0Pairs] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  refine ⟨h0.trans hp.1,
          h4.trans hPL,
          h5.trans hT0,
          h6.trans hT1,
          h7.trans hp.2.2.1,
          h8.trans hp.2.2.2.2.2.1,
          h9.trans hp.2.2.2.2.2.2.1,
          h10.trans hp.2.2.2.2.2.2.2.1,
          h11.trans hp.2.2.2.2.2.2.2.2.1,
          h12.trans hp.2.2.2.2.2.2.2.2.2.1,
          h13.trans hp.2.2.2.2.2.2.2.2.2.2.1,
          h14.trans hp.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro idx hlt; dsimp only; rw [h1]; exact hh_bits idx hlt
  · intro idx hlt; dsimp only; rw [h2]; exact hs_bits idx hlt
  · intro v hv; dsimp only; rw [h3]; exact hpre_bits v hv

/-!
# Section 3: Full Assembled `M_net` Register-Machine Programs (`rmMnetExact`, `rmMnetLe`, `rmMnetSep`)
-/

/-- Extract the state type of a `Branch8CircuitEmit.RMBlock`. -/
abbrev BlockQ {R : ℕ} {Q : Type} (_ : Branch8CircuitEmit.RMBlock R Q) : Type := Q

abbrev RMEmitBlocks0to9Q : Type := BlockQ Branch8CircuitEmit.blkEmitBlocks0to9

abbrev RMStage67Q : Type := RMEmitBlocks0to9Q ⊕ Branch8bTail.RMEmitBlocks10to18Q

def rmStage67 (mode : ℕ) : RMProg R_mnet RMStage67Q :=
  rmChain (rmLift embEmit Branch8CircuitEmit.rmEmitBlocks0to9)
    (rmLift embEnc (Branch8bTail.rmEmitBlocks10to18 mode))
    Branch8bTail.rmEmitBlocks10to18Entry

def rmStage67Entry : RMStage67Q :=
  rmChainEntry (rmLift embEmit Branch8CircuitEmit.rmEmitBlocks0to9)
    Branch8CircuitEmit.rmEmitBlocks0to9Entry
    Branch8bTail.rmEmitBlocks10to18Entry

def rmStage67Exit : RMStage67Q :=
  Sum.inr Branch8bTail.rmEmitBlocks10to18Exit

abbrev RMMnetCoreQ : Type :=
  RMComputeParamsQ ⊕
  (RMEmitNetHeaderQ ⊕
   (RMEmitAllEdgesQ ⊕
    (Fin 16 ⊕ RMStage67Q)))

def rmMnetCore (mode : ℕ) : RMProg R_mnet RMMnetCoreQ :=
  rmChain (rmLift embEnc rmComputeParams)
    (rmChain (rmLift embEnc rmEmitNetHeader)
      (rmChain (rmLift embEnc rmEmitAllEdges)
        (rmChain rmCopyTier0ToEmit
          (rmStage67 mode)
          rmStage67Entry)
        (Sum.inl rmCopyTier0ToEmitEntry))
      (Sum.inl rmEmitAllEdgesEntry))
    (Sum.inl rmEmitNetHeaderEntry)

def rmMnetCoreEntry : RMMnetCoreQ := Sum.inl rmComputeParamsEntry
def rmMnetCoreExit : RMMnetCoreQ := Sum.inr (Sum.inr (Sum.inr (Sum.inr rmStage67Exit)))

/-- Standard input parser followed by `regT1 := 0` (1 step) so `Exact`/`Le` share `rmMnetCore`. -/
abbrev RMParseStdZeroT1Q : Type := RMParseInputStdQ ⊕ Bool

def rmParseStdZeroT1 : RMProg R_mnet RMParseStdZeroT1Q :=
  rmChain (rmLift embEnc rmParseInputStd) (rmZero (embEnc regT1)) false

def rmParseStdZeroT1Entry : RMParseStdZeroT1Q := Sum.inl rmParseInputStdEntry
def rmParseStdZeroT1Exit : RMParseStdZeroT1Q := Sum.inr true

abbrev RMMnetExactQ : Type := RMParseStdZeroT1Q ⊕ RMMnetCoreQ
abbrev RMMnetLeQ : Type := RMParseStdZeroT1Q ⊕ RMMnetCoreQ
abbrev RMMnetSepQ : Type := RMParseInputSepQ ⊕ RMMnetCoreQ

def rmMnetExact : RMProg R_mnet RMMnetExactQ :=
  rmChain rmParseStdZeroT1 (rmMnetCore 0) rmMnetCoreEntry

def rmMnetExactEntry : RMMnetExactQ := Sum.inl rmParseStdZeroT1Entry
def rmMnetExactExit : RMMnetExactQ := Sum.inr rmMnetCoreExit

def rmMnetLe : RMProg R_mnet RMMnetLeQ :=
  rmChain rmParseStdZeroT1 (rmMnetCore 1) rmMnetCoreEntry

def rmMnetLeEntry : RMMnetLeQ := Sum.inl rmParseStdZeroT1Entry
def rmMnetLeExit : RMMnetLeQ := Sum.inr rmMnetCoreExit

def rmMnetSep : RMProg R_mnet RMMnetSepQ :=
  rmChain (rmLift embEnc rmParseInputSep) (rmMnetCore 2) rmMnetCoreEntry

def rmMnetSepEntry : RMMnetSepQ := Sum.inl rmParseInputSepEntry
def rmMnetSepExit : RMMnetSepQ := Sum.inr rmMnetCoreExit

/-- Uniform polynomial constants: `Vmax = mnetCV * (n + 1) ^ 2` and `T = mnetCT * (n + 1) ^ 4`. -/
def mnetCV : ℕ := 9000
def mnetCT : ℕ := 140000000000

private lemma mnetCore_step_bound (n vc ec : ℕ) (hn : 1 ≤ n)
    (hvc : vc ≤ 520 * (n + 1)) (hec : ec ≤ 520 * (n + 1)) :
    let V_enc := 520 * (n + 1)
    (200 * n * V_enc + 2210 * n ^ 2 + 4020 * n + 690) +
    ((2 * vc + 2 * ec + 6) +
     (2000000 * n ^ 3 +
      (15 +
       (16000000 * (520 + 8005) * (n + 1) ^ 4 +
        (100000 * n ^ 2 + 30 * V_enc + 5000))))) ≤
    137000000000 * (n + 1) ^ 4 := by
  intro V_enc
  have h1 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow 4 (n + 1) (by omega)
  have hlin : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by decide : 1 ≤ 4)
  have hsq : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
  have hcu : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 4)
  have hn_le : n ≤ n + 1 := Nat.le_succ n
  have hn2_le : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left hn_le 2
  have hn3_le : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left hn_le 3
  have hmul : n * (n + 1) ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right (n + 1) hn_le
  have hV2 : 200 * n * V_enc ≤ 104000 * (n + 1) ^ 2 := by
    have : 200 * n * V_enc = 104000 * (n * (n + 1)) := by dsimp only [V_enc]; ring
    rw [this]; exact Nat.mul_le_mul_left 104000 hmul
  have hS3 : 2 * vc + 2 * ec + 6 ≤ 2080 * (n + 1) + 6 := by omega
  have h30V : 30 * V_enc = 15600 * (n + 1) := by dsimp only [V_enc]; ring
  have hsmall :
      (200 * n * V_enc + 2210 * n ^ 2 + 4020 * n + 690) +
      (2 * vc + 2 * ec + 6) +
      2000000 * n ^ 3 + 15 + (100000 * n ^ 2 + 30 * V_enc + 5000) ≤
      600000000 * (n + 1) ^ 4 := by
    have ha : 200 * n * V_enc + 2210 * n ^ 2 + 4020 * n + 690 ≤ 200000 * (n + 1) ^ 4 := by linarith
    have hb : 2 * vc + 2 * ec + 6 ≤ 3000 * (n + 1) ^ 4 := by linarith
    have hc : 2000000 * n ^ 3 ≤ 2000000 * (n + 1) ^ 4 := by linarith
    have hd : 100000 * n ^ 2 + 30 * V_enc + 5000 ≤ 200000 * (n + 1) ^ 4 := by linarith
    linarith
  calc
    (200 * n * V_enc + 2210 * n ^ 2 + 4020 * n + 690) +
    ((2 * vc + 2 * ec + 6) +
     (2000000 * n ^ 3 +
      (15 +
       (16000000 * (520 + 8005) * (n + 1) ^ 4 +
        (100000 * n ^ 2 + 30 * V_enc + 5000)))))
        = ((200 * n * V_enc + 2210 * n ^ 2 + 4020 * n + 690) +
           (2 * vc + 2 * ec + 6) +
           2000000 * n ^ 3 + 15 + (100000 * n ^ 2 + 30 * V_enc + 5000)) +
          136400000000 * (n + 1) ^ 4 := by ring
    _ ≤ 600000000 * (n + 1) ^ 4 + 136400000000 * (n + 1) ^ 4 := Nat.add_le_add_right hsmall _
    _ = 137000000000 * (n + 1) ^ 4 := by ring

private lemma rmMnetCore_spec (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (pre inp : List Bool) (reg₀ : RegState R_mnet)
    (hn : 1 ≤ n)
    (hreg₀ : ∀ r, reg₀ r ≤ 520 * (n + 1))
    (hN : reg₀ (embEnc regN) = n)
    (hOffS : reg₀ (embEnc regOffS) = 2 * n + 1)
    (hT0 : reg₀ (embEnc regT0) = t0)
    (hT1 : reg₀ (embEnc regT1) = t1)
    (hPL : reg₀ (embEnc regPreLen) = pre.length)
    (hh_bits : ∀ (i : ℕ) (hi : i < n),
      inp.getD (reg₀ (embEnc regOffH) + i) false = decide (h ⟨i, hi⟩ = (1 : ZMod 2)))
    (hs_bits : ∀ (i : ℕ) (hi : i < n),
      inp.getD (reg₀ (embEnc regOffS) + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2)))
    (hpre_bits : ∀ i < pre.length,
      inp.getD (reg₀ (embEnc regOffPre) + i) false = pre.getD i false) :
    ∃ reg₁ : RegState R_mnet,
      RMExec (rmMnetCore mode) (mnetCV * (n + 1) ^ 2) inp rmMnetCoreEntry reg₀ rmMnetCoreExit reg₁
        (mnetMiddleStream mode n h s t0 t1 pre)
        (137000000000 * (n + 1) ^ 4) := by
  set V_enc := 520 * (n + 1)
  set Vmax := mnetCV * (n + 1) ^ 2
  have h500 : 500 * n + 20 ≤ V_enc := by dsimp only [V_enc]; omega
  have hn1_sq : n + 1 ≤ (n + 1) ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_right (n + 1) (by omega)
  have hV_enc_le_520sq : V_enc ≤ 520 * (n + 1) ^ 2 := Nat.mul_le_mul_left 520 hn1_sq
  have hV_enc_le_Vmax : V_enc ≤ Vmax := by
    dsimp only [Vmax, mnetCV]
    exact hV_enc_le_520sq.trans (Nat.mul_le_mul_right _ (by decide))
  -- Stage 2: rmComputeParams lifted to 0..55
  rcases rmComputeParams_spec n V_enc inp (fun j => reg₀ (embEnc j)) hn hN
      (fun j => hreg₀ (embEnc j)) h500
    with ⟨r2s, hp2, hpr2, e2s⟩
  rcases rmLift_spec embEnc embEnc_injective rmComputeParams V_enc V_enc inp
      rmComputeParamsEntry rmComputeParamsExit reg₀ r2s [] _
      (fun i _ => hreg₀ i) e2s
    with ⟨r2, h2_enc, h2_out, e2⟩
  rw [max_self] at e2
  have hp2' : ParamsLoaded n (fun j => r2 (embEnc j)) := by
    have : (fun j => r2 (embEnc j)) = r2s := funext h2_enc
    rw [this]; exact hp2
  have h2_keep : ∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → r2 (embEnc i) = reg₀ (embEnc i) :=
    fun i h1 h2 => (h2_enc i).trans (hpr2 i h1 h2)
  -- Stage 3: rmEmitNetHeader lifted to 0..55
  rcases rmEmitNetHeader_spec n V_enc inp (fun j => r2 (embEnc j)) hp2'
      (fun j => e2.reg₁_le (embEnc j))
    with ⟨r3s, hp3, hpr3, e3s⟩
  rcases rmLift_spec embEnc embEnc_injective rmEmitNetHeader V_enc V_enc inp
      rmEmitNetHeaderEntry rmEmitNetHeaderExit r2 r3s _ _
      (fun i _ => e2.reg₁_le i) e3s
    with ⟨r3, h3_enc, h3_out, e3⟩
  rw [max_self] at e3
  have hp3' : ParamsLoaded n (fun j => r3 (embEnc j)) := by
    have : (fun j => r3 (embEnc j)) = r3s := funext h3_enc
    rw [this]; exact hp3
  have h3_keep : ∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → r3 (embEnc i) = reg₀ (embEnc i) :=
    fun i h1 h2 => ((h3_enc i).trans (hpr3 i h1 h2)).trans (h2_keep i h1 h2)
  have hVC_le : Branch6Encoder.netVertCount n ≤ V_enc := by
    rw [← hp2'.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact e2.reg₁_le (embEnc regVertCount)
  have hEC_le : Branch6Encoder.netEdgeCount n ≤ V_enc := by
    rw [← hp2'.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact e2.reg₁_le (embEnc regEdgeCount)
  -- Stage 4: rmEmitAllEdges lifted to 0..55
  rcases rmEmitAllEdges_spec n V_enc inp (fun j => r3 (embEnc j)) hn hp3'
      (fun j => e3.reg₁_le (embEnc j)) h500
    with ⟨r4s, hp4, hpr4, e4s⟩
  rcases rmLift_spec embEnc embEnc_injective rmEmitAllEdges V_enc V_enc inp
      rmEmitAllEdgesEntry rmEmitAllEdgesExit r3 r4s _ _
      (fun i _ => e3.reg₁_le i) e4s
    with ⟨r4, h4_enc, h4_out, e4⟩
  rw [max_self] at e4
  have hp4' : ParamsLoaded n (fun j => r4 (embEnc j)) := by
    have : (fun j => r4 (embEnc j)) = r4s := funext h4_enc
    rw [this]; exact hp4
  have h4_keep : ∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → r4 (embEnc i) = reg₀ (embEnc i) :=
    fun i h1 h2 => ((h4_enc i).trans (hpr4 i h1 h2)).trans (h3_keep i h1 h2)
  -- Stage 5: rmCopyTier0ToEmit (0..55 preserved, 56..70 loaded with ValidTier0)
  rcases rmCopyTier0ToEmit_spec n V_enc h s t0 t1 pre inp r4 e4.reg₁_le hp4'
      ((h4_keep regT0 (by decide) (by decide)).trans hT0)
      ((h4_keep regT1 (by decide) (by decide)).trans hT1)
      ((h4_keep regPreLen (by decide) (by decide)).trans hPL)
      (by rw [h4_keep regOffH (by decide) (by decide)]; exact hh_bits)
      (by rw [h4_keep regOffS (by decide) (by decide)]; exact hs_bits)
      (by rw [h4_keep regOffPre (by decide) (by decide)]; exact hpre_bits)
    with ⟨r5, h5_enc, hT5, e5⟩
  -- Stage 6: rmEmitBlocks0to9 lifted to 56..97 (0..55 untouched!)
  have h5_emit_le : ∀ j : Fin Branch8CircuitEmit.R_emit, r5 (embEmit j) ≤ 520 * (n + 1) ^ 2 :=
    fun j => (e5.reg₁_le (embEmit j)).trans hV_enc_le_520sq
  have hVmax_ge : (520 + 8005) * (n + 1) ^ 2 ≤ Vmax :=
    Nat.mul_le_mul_right _ (by decide)
  rcases Branch8CircuitEmit.rmEmitBlocks0to9_quartic_spec mode n 520 Vmax h s t0 t1 pre inp
      (fun j => r5 (embEmit j)) hT5 h5_emit_le hVmax_ge
    with ⟨q6, r6s, _, e6s⟩
  rcases rmLift_spec embEmit embEmit_injective Branch8CircuitEmit.rmEmitBlocks0to9 Vmax Vmax inp
      Branch8CircuitEmit.rmEmitBlocks0to9Entry q6 r5 r6s _ _
      (fun i _ => (e5.reg₁_le i).trans hV_enc_le_Vmax) e6s
    with ⟨r6, _, h6_out, e6⟩
  rw [max_self] at e6
  have h6_enc : ∀ j : Fin EncR, r6 (embEnc j) = r4 (embEnc j) := fun j =>
    (h6_out (embEnc j) (fun k heq => embEnc_ne_embEmit j k heq.symm)).trans (h5_enc j)
  have hp6' : ParamsLoaded n (fun j => r6 (embEnc j)) := by
    have : (fun j => r6 (embEnc j)) = (fun j => r4 (embEnc j)) := funext h6_enc
    rw [this]; exact hp4'
  -- Stage 7: rmEmitBlocks10to18 lifted to 0..55 (at V₁ = V_enc, V₂ = Vmax)
  have h6_enc_le : ∀ j : Fin EncR, r6 (embEnc j) ≤ V_enc := fun j => by
    rw [h6_enc j]; exact e4.reg₁_le (embEnc j)
  have h6_offS : r6 (embEnc regOffS) + n ≤ V_enc := by
    rw [h6_enc regOffS, h4_keep regOffS (by decide) (by decide), hOffS]
    dsimp only [V_enc]; omega
  rcases Branch8bTail.rmEmitBlocks10to18_spec_V mode n V_enc s t0 t1 inp
      (fun j => r6 (embEnc j)) hn hp6' h6_enc_le h500 h6_offS
      ((h6_enc regT0).trans ((h4_keep regT0 (by decide) (by decide)).trans hT0))
      ((h6_enc regT1).trans ((h4_keep regT1 (by decide) (by decide)).trans hT1))
      (by rw [h6_enc regOffS, h4_keep regOffS (by decide) (by decide)]; exact hs_bits)
    with ⟨r7s, _, _, e7s⟩
  rcases rmLift_spec embEnc embEnc_injective (Branch8bTail.rmEmitBlocks10to18 mode) V_enc Vmax inp
      Branch8bTail.rmEmitBlocks10to18Entry Branch8bTail.rmEmitBlocks10to18Exit r6 r7s _ _
      (fun i _ => e6.reg₁_le i) e7s
    with ⟨r7, _, _, e7⟩
  have hmax7 : max V_enc Vmax = Vmax := Nat.max_eq_right hV_enc_le_Vmax
  rw [hmax7] at e7
  -- Chain Stages 2..7
  have e67 := rmChain_spec e6 e7
  rw [max_self] at e67
  have hact5 : rmCopyTier0ToEmit rmCopyTier0ToEmitEntry ≠ none := by
    simp [rmCopyTier0ToEmit, rmCopyTier0ToEmitEntry]
  have e57 := rmChain_spec_inl hact5 e5 e67
  rw [hmax7, List.nil_append] at e57
  have hact4 : rmLift embEnc rmEmitAllEdges rmEmitAllEdgesEntry ≠ none := by
    simp [rmLift, rmEmitAllEdges, rmEmitAllEdgesEntry, rmEmitG0, rmEmitB0,
      rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]
  have e47 := rmChain_spec_inl hact4 e4 e57
  rw [hmax7] at e47
  have hact3 : rmLift embEnc rmEmitNetHeader rmEmitNetHeaderEntry ≠ none := by
    simp [rmLift, rmEmitNetHeader, rmEmitNetHeaderEntry, rmEmitUnary, rmEmitUnaryEntry,
      rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmChain, rmSeq, rmCopy]
  have e37 := rmChain_spec_inl hact3 e3 e47
  rw [hmax7] at e37
  have hact2 : rmLift embEnc rmComputeParams rmComputeParamsEntry ≠ none := by
    simp [rmLift, rmComputeParams, rmComputeParamsEntry, rmParamsA1, rmParamsA1Entry,
      rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have e27 := rmChain_spec_inl hact2 e2 e37
  rw [hmax7, List.nil_append] at e27
  -- Output stream equality
  have hout :
      (QCSD_natToUnary (Branch6Encoder.netVertCount n) ++ QCSD_natToUnary (Branch6Encoder.netEdgeCount n)) ++
      ((List.range (Branch6Encoder.netEdgeCount n)).flatMap (fun e =>
        QCSD_natToUnary (Branch6Encoder.rawEnds n e).1 ++ QCSD_natToUnary (Branch6Encoder.rawEnds n e).2) ++
       ((List.range (Branch8CircuitEmit.netV10 n)).flatMap
         (fun v => QCSD_encodeCircuit (Branch8CircuitEmit.rawPred mode n h s t0 t1 pre v)) ++
        (List.range (Branch6Encoder.netVertCount n - Branch6Encoder.netV10 n)).flatMap
         (fun d => QCSD_encodeCircuit (Branch8bTail.rawPredTail mode n s t0 t1 (Branch6Encoder.netV10 n + d))))) =
      mnetMiddleStream mode n h s t0 t1 pre := by
    rw [← List.append_assoc]
    exact mnet_concat_eq_middleStream mode n h s t0 t1 pre
  rw [hout] at e27
  -- Step bound
  have hT_le := mnetCore_step_bound n (Branch6Encoder.netVertCount n)
    (Branch6Encoder.netEdgeCount n) hn hVC_le hEC_le
  exact ⟨r7, e27.weaken le_rfl hT_le⟩

/-- **Full `M_net` Register-Machine Specification (`Exact`, `mode = 0`)**:
Starting from all-zero registers (`fun _ => 0`) on `QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre`,
`rmMnetExact` halts at `rmMnetExactExit` emitting `mnetMiddleStream 0 x.n x.h x.s x.t 0 pre`
(matching `encodeNet2_padNet_N_exact_stream_split_exact`) with register bound
`mnetCV * (x.n + 1) ^ 2` and step count `mnetCT * (x.n + 1) ^ 4`. -/
theorem rmMnetExact_spec (x : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ x.n) (ht : x.t ≤ 2 * x.n) (hpre : pre.length ≤ 2 * x.n) :
    let inp := QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre
    ∃ reg₁ : RegState R_mnet,
      RMExec rmMnetExact (mnetCV * (x.n + 1) ^ 2) inp
        rmMnetExactEntry (fun _ => 0) rmMnetExactExit reg₁
        (mnetMiddleStream 0 x.n x.h x.s x.t 0 pre)
        (mnetCT * (x.n + 1) ^ 4) := by
  intro inp
  set V_enc := 520 * (x.n + 1)
  have hlen_inp : inp.length ≤ V_enc := by
    simp only [inp, QCSD_encodeInstance, List.length_append,
      Branch6Encoder.natToUnary_length, Branch6Encoder.vecToBits_length, V_enc]
    omega
  rcases rmParseInputStd_spec x pre V_enc (fun _ => 0) (fun _ => Nat.zero_le _) hlen_inp
    with ⟨r1s, h1n, h1oH, h1oS, h1t0, h1pl, h1oP, h1h, h1s, h1p, e1s⟩
  rcases rmLift_spec embEnc embEnc_injective rmParseInputStd V_enc V_enc inp
      rmParseInputStdEntry rmParseInputStdExit (fun _ => 0) r1s [] _
      (fun _ _ => Nat.zero_le _) e1s
    with ⟨r1, h1_enc, _, e1⟩
  rw [max_self] at e1
  have ez := rmZero_spec (embEnc regT1) V_enc inp r1 e1.reg₁_le
  have hact1 : rmLift embEnc rmParseInputStd rmParseInputStdEntry ≠ none := by
    simp [rmLift, rmParseInputStd, rmParseInputStdEntry, rmParsePrefix, rmParsePrefixEntry,
      rmChain, rmSeq, rmZero]
  have eParse := rmChain_spec_inl hact1 e1 ez
  rw [max_self, List.nil_append] at eParse
  set r1' := regUpd r1 (embEnc regT1) 0
  have hne : ∀ j : Fin EncR, j ≠ regT1 → r1' (embEnc j) = r1s j := fun j hj => by
    dsimp only [r1']
    rw [regUpd_ne r1 (fun h => hj (embEnc_injective h)), h1_enc j]
  rcases rmMnetCore_spec 0 x.n x.h x.s x.t 0 pre inp r1' hn eParse.reg₁_le
      ((hne regN (by decide)).trans h1n)
      ((hne regOffS (by decide)).trans h1oS)
      ((hne regT0 (by decide)).trans h1t0)
      (regUpd_self r1 (embEnc regT1) 0)
      ((hne regPreLen (by decide)).trans h1pl)
      (by rw [hne regOffH (by decide)]; exact h1h)
      (by rw [hne regOffS (by decide)]; exact h1s)
      (by rw [hne regOffPre (by decide)]; exact h1p)
    with ⟨r_end, eCore⟩
  have hactP : rmParseStdZeroT1 rmParseStdZeroT1Entry ≠ none := by
    simp [rmParseStdZeroT1, rmParseStdZeroT1Entry, rmLift, rmParseInputStd, rmParseInputStdEntry,
      rmParsePrefix, rmParsePrefixEntry, rmChain, rmSeq, rmZero]
  have eAll := rmChain_spec_inl hactP eParse eCore
  have hV_le : V_enc ≤ mnetCV * (x.n + 1) ^ 2 := by
    have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [V_enc, mnetCV]
    exact (Nat.mul_le_mul_left 520 hsq).trans (Nat.mul_le_mul_right _ (by decide))
  rw [Nat.max_eq_right hV_le, List.nil_append] at eAll
  have hT_le : (7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1) + 137000000000 * (x.n + 1) ^ 4 ≤
      mnetCT * (x.n + 1) ^ 4 := by
    have h1 : 1 ≤ (x.n + 1) ^ 4 := Nat.one_le_pow 4 (x.n + 1) (by omega)
    have hlin : x.n + 1 ≤ (x.n + 1) ^ 4 := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ x.n + 1) (by decide : 1 ≤ 4)
    have hsmall : 7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1 ≤ 3000000000 * (x.n + 1) ^ 4 := by
      omega
    calc
      (7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1) + 137000000000 * (x.n + 1) ^ 4
          ≤ 3000000000 * (x.n + 1) ^ 4 + 137000000000 * (x.n + 1) ^ 4 := Nat.add_le_add_right hsmall _
      _ = mnetCT * (x.n + 1) ^ 4 := by dsimp only [mnetCT]; ring
  exact ⟨r_end, eAll.weaken le_rfl hT_le⟩

/-- **Full `M_net` Register-Machine Specification (`Le`, `mode = 1`)**:
Identical to `rmMnetExact_spec` for `Branch3.N_le`. -/
theorem rmMnetLe_spec (x : QCSD_Instance) (pre : List Bool)
    (hn : 1 ≤ x.n) (ht : x.t ≤ 2 * x.n) (hpre : pre.length ≤ 2 * x.n) :
    let inp := QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre
    ∃ reg₁ : RegState R_mnet,
      RMExec rmMnetLe (mnetCV * (x.n + 1) ^ 2) inp
        rmMnetLeEntry (fun _ => 0) rmMnetLeExit reg₁
        (mnetMiddleStream 1 x.n x.h x.s x.t 0 pre)
        (mnetCT * (x.n + 1) ^ 4) := by
  intro inp
  set V_enc := 520 * (x.n + 1)
  have hlen_inp : inp.length ≤ V_enc := by
    simp only [inp, QCSD_encodeInstance, List.length_append,
      Branch6Encoder.natToUnary_length, Branch6Encoder.vecToBits_length, V_enc]
    omega
  rcases rmParseInputStd_spec x pre V_enc (fun _ => 0) (fun _ => Nat.zero_le _) hlen_inp
    with ⟨r1s, h1n, h1oH, h1oS, h1t0, h1pl, h1oP, h1h, h1s, h1p, e1s⟩
  rcases rmLift_spec embEnc embEnc_injective rmParseInputStd V_enc V_enc inp
      rmParseInputStdEntry rmParseInputStdExit (fun _ => 0) r1s [] _
      (fun _ _ => Nat.zero_le _) e1s
    with ⟨r1, h1_enc, _, e1⟩
  rw [max_self] at e1
  have ez := rmZero_spec (embEnc regT1) V_enc inp r1 e1.reg₁_le
  have hact1 : rmLift embEnc rmParseInputStd rmParseInputStdEntry ≠ none := by
    simp [rmLift, rmParseInputStd, rmParseInputStdEntry, rmParsePrefix, rmParsePrefixEntry,
      rmChain, rmSeq, rmZero]
  have eParse := rmChain_spec_inl hact1 e1 ez
  rw [max_self, List.nil_append] at eParse
  set r1' := regUpd r1 (embEnc regT1) 0
  have hne : ∀ j : Fin EncR, j ≠ regT1 → r1' (embEnc j) = r1s j := fun j hj => by
    dsimp only [r1']
    rw [regUpd_ne r1 (fun h => hj (embEnc_injective h)), h1_enc j]
  rcases rmMnetCore_spec 1 x.n x.h x.s x.t 0 pre inp r1' hn eParse.reg₁_le
      ((hne regN (by decide)).trans h1n)
      ((hne regOffS (by decide)).trans h1oS)
      ((hne regT0 (by decide)).trans h1t0)
      (regUpd_self r1 (embEnc regT1) 0)
      ((hne regPreLen (by decide)).trans h1pl)
      (by rw [hne regOffH (by decide)]; exact h1h)
      (by rw [hne regOffS (by decide)]; exact h1s)
      (by rw [hne regOffPre (by decide)]; exact h1p)
    with ⟨r_end, eCore⟩
  have hactP : rmParseStdZeroT1 rmParseStdZeroT1Entry ≠ none := by
    simp [rmParseStdZeroT1, rmParseStdZeroT1Entry, rmLift, rmParseInputStd, rmParseInputStdEntry,
      rmParsePrefix, rmParsePrefixEntry, rmChain, rmSeq, rmZero]
  have eAll := rmChain_spec_inl hactP eParse eCore
  have hV_le : V_enc ≤ mnetCV * (x.n + 1) ^ 2 := by
    have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [V_enc, mnetCV]
    exact (Nat.mul_le_mul_left 520 hsq).trans (Nat.mul_le_mul_right _ (by decide))
  rw [Nat.max_eq_right hV_le, List.nil_append] at eAll
  have hT_le : (7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1) + 137000000000 * (x.n + 1) ^ 4 ≤
      mnetCT * (x.n + 1) ^ 4 := by
    have h1 : 1 ≤ (x.n + 1) ^ 4 := Nat.one_le_pow 4 (x.n + 1) (by omega)
    have hlin : x.n + 1 ≤ (x.n + 1) ^ 4 := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ x.n + 1) (by decide : 1 ≤ 4)
    have hsmall : 7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1 ≤ 3000000000 * (x.n + 1) ^ 4 := by
      omega
    calc
      (7 * x.n + 3 * x.t + 3 * pre.length + 17 + 1) + 137000000000 * (x.n + 1) ^ 4
          ≤ 3000000000 * (x.n + 1) ^ 4 + 137000000000 * (x.n + 1) ^ 4 := Nat.add_le_add_right hsmall _
      _ = mnetCT * (x.n + 1) ^ 4 := by dsimp only [mnetCT]; ring
  exact ⟨r_end, eAll.weaken le_rfl hT_le⟩

/-- **Full `M_net` Register-Machine Specification (`Sep`, `mode = 2`)**:
Starting from all-zero registers on `QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre`,
`rmMnetSep` halts at `rmMnetSepExit` emitting `mnetMiddleStream 2 x.n x.h x.s x.t₀ x.t₁ pre`
(matching `encodeNet2_padNet_N_sep_stream_split_exact`) with register bound
`mnetCV * (x.n + 1) ^ 2` and step count `mnetCT * (x.n + 1) ^ 4`. -/
theorem rmMnetSep_spec (x : QCSD_InstanceSep) (pre : List Bool)
    (hn : 1 ≤ x.n) (ht0 : x.t₀ ≤ x.n) (ht1 : x.t₁ ≤ x.n) (hpre : pre.length ≤ 2 * x.n) :
    let inp := QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre
    ∃ reg₁ : RegState R_mnet,
      RMExec rmMnetSep (mnetCV * (x.n + 1) ^ 2) inp
        rmMnetSepEntry (fun _ => 0) rmMnetSepExit reg₁
        (mnetMiddleStream 2 x.n x.h x.s x.t₀ x.t₁ pre)
        (mnetCT * (x.n + 1) ^ 4) := by
  intro inp
  set V_enc := 520 * (x.n + 1)
  have hlen_inp : inp.length ≤ V_enc := by
    simp only [inp, QCSD_encodeInstanceSep, List.length_append,
      Branch6Encoder.natToUnary_length, Branch6Encoder.vecToBits_length, V_enc]
    omega
  rcases rmParseInputSep_spec x pre V_enc (fun _ => 0) (fun _ => Nat.zero_le _) hlen_inp
    with ⟨r1s, h1n, h1oH, h1oS, h1t0, h1t1, h1pl, h1oP, h1h, h1s, h1p, e1s⟩
  rcases rmLift_spec embEnc embEnc_injective rmParseInputSep V_enc V_enc inp
      rmParseInputSepEntry rmParseInputSepExit (fun _ => 0) r1s [] _
      (fun _ _ => Nat.zero_le _) e1s
    with ⟨r1, h1_enc, _, e1⟩
  rw [max_self] at e1
  rcases rmMnetCore_spec 2 x.n x.h x.s x.t₀ x.t₁ pre inp r1 hn e1.reg₁_le
      ((h1_enc regN).trans h1n)
      ((h1_enc regOffS).trans h1oS)
      ((h1_enc regT0).trans h1t0)
      ((h1_enc regT1).trans h1t1)
      ((h1_enc regPreLen).trans h1pl)
      (by rw [h1_enc regOffH]; exact h1h)
      (by rw [h1_enc regOffS]; exact h1s)
      (by rw [h1_enc regOffPre]; exact h1p)
    with ⟨r_end, eCore⟩
  have hact1 : rmLift embEnc rmParseInputSep rmParseInputSepEntry ≠ none := by
    simp [rmLift, rmParseInputSep, rmParseInputSepEntry, rmParsePrefix, rmParsePrefixEntry,
      rmChain, rmSeq, rmZero]
  have eAll := rmChain_spec_inl hact1 e1 eCore
  have hV_le : V_enc ≤ mnetCV * (x.n + 1) ^ 2 := by
    have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [V_enc, mnetCV]
    exact (Nat.mul_le_mul_left 520 hsq).trans (Nat.mul_le_mul_right _ (by decide))
  rw [Nat.max_eq_right hV_le, List.nil_append] at eAll
  have hT_le : (7 * x.n + 3 * x.t₀ + 3 * x.t₁ + 3 * pre.length + 20) + 137000000000 * (x.n + 1) ^ 4 ≤
      mnetCT * (x.n + 1) ^ 4 := by
    have h1 : 1 ≤ (x.n + 1) ^ 4 := Nat.one_le_pow 4 (x.n + 1) (by omega)
    have hlin : x.n + 1 ≤ (x.n + 1) ^ 4 := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ x.n + 1) (by decide : 1 ≤ 4)
    have hsmall : 7 * x.n + 3 * x.t₀ + 3 * x.t₁ + 3 * pre.length + 20 ≤ 3000000000 * (x.n + 1) ^ 4 := by
      omega
    calc
      (7 * x.n + 3 * x.t₀ + 3 * x.t₁ + 3 * pre.length + 20) + 137000000000 * (x.n + 1) ^ 4
          ≤ 3000000000 * (x.n + 1) ^ 4 + 137000000000 * (x.n + 1) ^ 4 := Nat.add_le_add_right hsmall _
      _ = mnetCT * (x.n + 1) ^ 4 := by dsimp only [mnetCT]; ring
  exact ⟨r_end, eAll.weaken le_rfl hT_le⟩

/-!
# Section 4: Explicit Bottom-Up `Fintype` and `DecidableEq` Witnesses (Zero `instance` Declarations)

Constructed cleanly via `ftSum`/`deSum` so downstream `Branch4_TMCompiler.compileRMProgWithInit`
compiles instantaneously without triggering deep nested-`Sum` typeclass synthesis.
-/

private abbrev ftSum {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α ⊕ β) := by
  letI := hα; letI := hβ; exact inferInstance

private def deSum {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α ⊕ β) := by
  letI := hα; letI := hβ; exact inferInstance

private abbrev ftForRange {Q : Type} (hQ : Fintype Q) : Fintype (RMForRangeQ Q) := by
  letI := hQ; exact inferInstance

private def deForRange {Q : Type} (hQ : DecidableEq Q) : DecidableEq (RMForRangeQ Q) := by
  letI := hQ; exact inferInstance

-- Base macro types (`Branch6_EncoderMacros`)
private abbrev ftSetConst (c : ℕ) : Fintype (RMSetConstQ c) := ftSum inferInstance (Fin.fintype _)
private def deSetConst (c : ℕ) : DecidableEq (RMSetConstQ c) := deSum inferInstance inferInstance

private abbrev ftRMAdd : Fintype RMAddQ := inferInstance
private def deRMAdd : DecidableEq RMAddQ := inferInstance

private abbrev ftRMSub : Fintype RMSubQ := inferInstance
private def deRMSub : DecidableEq RMSubQ := inferInstance

private abbrev ftRMMul : Fintype RMMulQ :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance ftRMAdd)))
private def deRMMul : DecidableEq RMMulQ :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance deRMAdd)))

private abbrev ftRMDivMod : Fintype RMDivModQ :=
  have hBody : Fintype RMDivBodyQ := ftSum ftRMSub (ftSum inferInstance (Fin.fintype _))
  ftSum inferInstance (ftSum inferInstance (ftSum (Fin.fintype _)
    (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hBody)))))

private def deRMDivMod : DecidableEq RMDivModQ :=
  have hBody : DecidableEq RMDivBodyQ := deSum deRMSub (deSum inferInstance inferInstance)
  deSum inferInstance (deSum inferInstance (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum inferInstance hBody)))))

private abbrev ftRMPow : Fintype RMPowQ :=
  have hBody : Fintype RMPowBodyQ := ftSum ftRMMul inferInstance
  ftSum (ftSetConst 1) (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hBody)))

private def deRMPow : DecidableEq RMPowQ :=
  have hBody : DecidableEq RMPowBodyQ := deSum deRMMul inferInstance
  deSum (deSetConst 1) (deSum inferInstance (deSum inferInstance (deSum inferInstance hBody)))

private abbrev ftRMMinPowExp : Fintype RMMinPowExpQ :=
  have hBody : Fintype RMMinPowBodyQ :=
    ftSum inferInstance (ftSum ftRMMul (ftSum inferInstance (Fin.fintype _)))
  ftSum inferInstance (ftSum (ftSetConst 1) (ftSum (Fin.fintype _)
    (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hBody)))))

private def deRMMinPowExp : DecidableEq RMMinPowExpQ :=
  have hBody : DecidableEq RMMinPowBodyQ :=
    deSum inferInstance (deSum deRMMul (deSum inferInstance inferInstance))
  deSum inferInstance (deSum (deSetConst 1) (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum inferInstance hBody)))))

private abbrev ftRMEmitUnary : Fintype RMEmitUnaryQ := inferInstance
private def deRMEmitUnary : DecidableEq RMEmitUnaryQ := inferInstance

private abbrev ftRMReadUnary : Fintype RMReadUnaryQ := inferInstance
private def deRMReadUnary : DecidableEq RMReadUnaryQ := inferInstance

private abbrev ftRMSetAdd : Fintype RMSetAddQ := ftSum inferInstance ftRMAdd
private def deRMSetAdd : DecidableEq RMSetAddQ := deSum inferInstance deRMAdd

private abbrev ftRMEmitEndPair : Fintype RMEmitEndPairQ := ftSum ftRMEmitUnary ftRMEmitUnary
private def deRMEmitEndPair : DecidableEq RMEmitEndPairQ := deSum deRMEmitUnary deRMEmitUnary

-- Input parsers (`Branch6b_ParseAndEdges`)
private abbrev ftRMParsePrefix : Fintype RMParsePrefixQ :=
  ftSum inferInstance (ftSum ftRMReadUnary (ftSum inferInstance
    (ftSum ftRMAdd (ftSum inferInstance ftRMAdd))))

private def deRMParsePrefix : DecidableEq RMParsePrefixQ :=
  deSum inferInstance (deSum deRMReadUnary (deSum inferInstance
    (deSum deRMAdd (deSum inferInstance deRMAdd))))

private abbrev ftRMParseInputStd : Fintype RMParseInputStdQ :=
  ftSum ftRMParsePrefix (ftSum ftRMReadUnary (ftSum ftRMReadUnary inferInstance))

private def deRMParseInputStd : DecidableEq RMParseInputStdQ :=
  deSum deRMParsePrefix (deSum deRMReadUnary (deSum deRMReadUnary inferInstance))

private abbrev ftRMParseInputSep : Fintype RMParseInputSepQ :=
  ftSum ftRMParsePrefix (ftSum ftRMReadUnary (ftSum ftRMReadUnary (ftSum ftRMReadUnary inferInstance)))

private def deRMParseInputSep : DecidableEq RMParseInputSepQ :=
  deSum deRMParsePrefix (deSum deRMReadUnary (deSum deRMReadUnary (deSum deRMReadUnary inferInstance)))

-- Parameter computation (`Branch6b_ParseAndEdges`)
private abbrev ftRMParamsA1 : Fintype RMParamsA1Q :=
  ftSum (ftSetConst 9) (ftSum ftRMMinPowExp (ftSum (ftSetConst 3) (ftSum ftRMPow
    (ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum ftRMDivMod
      (ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance
        (ftSum (ftSetConst 3) ftRMMinPowExp)))))))))))

private def deRMParamsA1 : DecidableEq RMParamsA1Q :=
  deSum (deSetConst 9) (deSum deRMMinPowExp (deSum (deSetConst 3) (deSum deRMPow
    (deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum deRMDivMod
      (deSum inferInstance (deSum deRMAdd (deSum inferInstance
        (deSum (deSetConst 3) deRMMinPowExp)))))))))))

private abbrev ftRMParamsA2 : Fintype RMParamsA2Q :=
  ftSum (ftSetConst 2) (ftSum ftRMDivMod (ftSum (ftSetConst 3) (ftSum ftRMPow
    (ftSum inferInstance (ftSum inferInstance (ftSum (ftSetConst 2) (ftSum ftRMDivMod
      (ftSum (ftSetConst 3) (ftSum ftRMPow (ftSum inferInstance (ftSum inferInstance
        (ftSum ftRMSub (ftSum (ftSetConst 3) (ftSum ftRMPow (ftSum (ftSetConst 3)
          (ftSum ftRMMul (ftSum ftRMSub (ftSum inferInstance (ftSum ftRMAdd ftRMMul)))))))))))))))))))

private def deRMParamsA2 : DecidableEq RMParamsA2Q :=
  deSum (deSetConst 2) (deSum deRMDivMod (deSum (deSetConst 3) (deSum deRMPow
    (deSum inferInstance (deSum inferInstance (deSum (deSetConst 2) (deSum deRMDivMod
      (deSum (deSetConst 3) (deSum deRMPow (deSum inferInstance (deSum inferInstance
        (deSum deRMSub (deSum (deSetConst 3) (deSum deRMPow (deSum (deSetConst 3)
          (deSum deRMMul (deSum deRMSub (deSum inferInstance (deSum deRMAdd deRMMul)))))))))))))))))))

private abbrev ftRMParamsTree : Fintype RMParamsTreeQ :=
  ftSum (ftSetConst 2) (ftSum ftRMMinPowExp
    (ftSum inferInstance (ftSum (ftSum inferInstance ftRMAdd) (ftSum inferInstance inferInstance))))

private def deRMParamsTree : DecidableEq RMParamsTreeQ :=
  deSum (deSetConst 2) (deSum deRMMinPowExp
    (deSum inferInstance (deSum (deSum inferInstance deRMAdd) (deSum inferInstance inferInstance))))

private abbrev ftRMParamsV1to13 : Fintype RMParamsV1to13Q :=
  ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd
    (ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd (ftSum ftRMSetAdd
      (ftSum ftRMSetAdd (ftSum ftRMSetAdd ftRMSetAdd)))))))))))

private def deRMParamsV1to13 : DecidableEq RMParamsV1to13Q :=
  deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd
    (deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd (deSum deRMSetAdd
      (deSum deRMSetAdd (deSum deRMSetAdd deRMSetAdd)))))))))))

private abbrev ftRMParamsV14toEdge : Fintype RMParamsV14toEdgeQ :=
  ftSum inferInstance (ftSum ftRMSub (ftSum ftRMSetAdd (ftSum ftRMSetAdd
    (ftSum (ftSetConst 6) (ftSum ftRMMul (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum ftRMSub
      (ftSum ftRMSetAdd (ftSum inferInstance (ftSum inferInstance (ftSum ftRMSetAdd
        (ftSum (Fin.fintype _) (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
          (ftSum ftRMSetAdd (ftSum ftRMAdd (ftSum ftRMAdd (ftSum (ftSetConst 7) (ftSum ftRMMul
            (ftSum ftRMAdd (ftSum ftRMAdd (ftSum (ftSetConst 10) (ftSum ftRMMul
              (ftSum ftRMSetAdd (ftSum (Fin.fintype _) (ftSum ftRMSub
                (ftSum ftRMAdd (ftSum ftRMAdd (Fin.fintype _)))))))))))))))))))))))))))))))

private def deRMParamsV14toEdge : DecidableEq RMParamsV14toEdgeQ :=
  deSum inferInstance (deSum deRMSub (deSum deRMSetAdd (deSum deRMSetAdd
    (deSum (deSetConst 6) (deSum deRMMul (deSum inferInstance (deSum inferInstance (deSum deRMSub
      (deSum deRMSetAdd (deSum inferInstance (deSum inferInstance (deSum deRMSetAdd
        (deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance
          (deSum deRMSetAdd (deSum deRMAdd (deSum deRMAdd (deSum (deSetConst 7) (deSum deRMMul
            (deSum deRMAdd (deSum deRMAdd (deSum (deSetConst 10) (deSum deRMMul
              (deSum deRMSetAdd (deSum inferInstance (deSum deRMSub
                (deSum deRMAdd (deSum deRMAdd inferInstance))))))))))))))))))))))))))))))

private abbrev ftRMComputeParams : Fintype RMComputeParamsQ :=
  ftSum ftRMParamsA1 (ftSum ftRMParamsA2 (ftSum ftRMParamsTree
    (ftSum ftRMParamsV1to13 ftRMParamsV14toEdge)))

private def deRMComputeParams : DecidableEq RMComputeParamsQ :=
  deSum deRMParamsA1 (deSum deRMParamsA2 (deSum deRMParamsTree
    (deSum deRMParamsV1to13 deRMParamsV14toEdge)))

-- Edge emitter (`Branch6b_ParseAndEdges`)
private abbrev ftRMEmitB0 : Fintype RMEmitB0Q :=
  ftForRange (ftSum inferInstance (ftSum ftRMSetAdd ftRMEmitEndPair))

private def deRMEmitB0 : DecidableEq RMEmitB0Q :=
  deForRange (deSum inferInstance (deSum deRMSetAdd deRMEmitEndPair))

private abbrev ftRMEmitB1 : Fintype RMEmitB1Q :=
  have hElse : Fintype RMB1ElseQ :=
    ftSum inferInstance (ftSum ftRMSub (ftSum ftRMDivMod (ftSum ftRMDivMod ftRMSetAdd)))
  have hIf : Fintype RMB1IfQ := ftSum inferInstance (ftSum hElse (ftSum inferInstance ftRMSetAdd))
  ftForRange (ftSum ftRMSetAdd (ftSum (Fin.fintype _) (ftSum hIf ftRMEmitEndPair)))

private def deRMEmitB1 : DecidableEq RMEmitB1Q :=
  have hElse : DecidableEq RMB1ElseQ :=
    deSum inferInstance (deSum deRMSub (deSum deRMDivMod (deSum deRMDivMod deRMSetAdd)))
  have hIf : DecidableEq RMB1IfQ := deSum inferInstance (deSum hElse (deSum inferInstance deRMSetAdd))
  deForRange (deSum deRMSetAdd (deSum inferInstance (deSum hIf deRMEmitEndPair)))

private abbrev ftRMEmitB2 : Fintype RMEmitB2Q :=
  have hDst : Fintype RMB2DstQ :=
    ftSum (ftSetConst 2) (ftSum ftRMDivMod (ftSum ftRMSetAdd (ftSum ftRMSetAdd inferInstance)))
  have hBr3E : Fintype RMB2Br3ElseQ := ftSum inferInstance (ftSum ftRMSub ftRMSetAdd)
  have hBr3T : Fintype RMB2Br3ThenQ := ftSum inferInstance (ftSum ftRMSub (ftSum ftRMSetAdd ftRMSetAdd))
  have hBr3 : Fintype RMB2Br3Q :=
    ftSum (Fin.fintype _) (ftSum inferInstance (ftSum hBr3E (ftSum inferInstance hBr3T)))
  have hBr2T : Fintype RMB2Br2ThenQ := ftSum inferInstance (ftSum ftRMSub ftRMSetAdd)
  have hBr2 : Fintype RMB2Br2Q :=
    ftSum (Fin.fintype _) (ftSum inferInstance (ftSum hBr3 (ftSum inferInstance hBr2T)))
  have hSrc : Fintype RMB2SrcQ :=
    ftSum ftRMSetAdd (ftSum (Fin.fintype _) (ftSum inferInstance (ftSum hBr2 (ftSum inferInstance ftRMSetAdd))))
  ftSum ftRMSetAdd (ftForRange (ftSum hDst (ftSum hSrc ftRMEmitEndPair)))

private def deRMEmitB2 : DecidableEq RMEmitB2Q :=
  have hDst : DecidableEq RMB2DstQ :=
    deSum (deSetConst 2) (deSum deRMDivMod (deSum deRMSetAdd (deSum deRMSetAdd inferInstance)))
  have hBr3E : DecidableEq RMB2Br3ElseQ := deSum inferInstance (deSum deRMSub deRMSetAdd)
  have hBr3T : DecidableEq RMB2Br3ThenQ := deSum inferInstance (deSum deRMSub (deSum deRMSetAdd deRMSetAdd))
  have hBr3 : DecidableEq RMB2Br3Q :=
    deSum inferInstance (deSum inferInstance (deSum hBr3E (deSum inferInstance hBr3T)))
  have hBr2T : DecidableEq RMB2Br2ThenQ := deSum inferInstance (deSum deRMSub deRMSetAdd)
  have hBr2 : DecidableEq RMB2Br2Q :=
    deSum inferInstance (deSum inferInstance (deSum hBr3 (deSum inferInstance hBr2T)))
  have hSrc : DecidableEq RMB2SrcQ :=
    deSum deRMSetAdd (deSum inferInstance (deSum inferInstance (deSum hBr2 (deSum inferInstance deRMSetAdd))))
  deSum deRMSetAdd (deForRange (deSum hDst (deSum hSrc deRMEmitEndPair)))

private abbrev ftRMEmitB3 : Fintype RMEmitB3Q :=
  ftForRange (ftSum ftRMSetAdd (ftSum ftRMDivMod (ftSum ftRMDivMod (ftSum ftRMSetAdd ftRMEmitEndPair))))

private def deRMEmitB3 : DecidableEq RMEmitB3Q :=
  deForRange (deSum deRMSetAdd (deSum deRMDivMod (deSum deRMDivMod (deSum deRMSetAdd deRMEmitEndPair))))

private abbrev ftRMEmitDivModPair : Fintype RMEmitDivModPairQ :=
  ftForRange (ftSum ftRMDivMod (ftSum ftRMDivMod (ftSum ftRMSetAdd (ftSum ftRMSetAdd ftRMEmitEndPair))))

private def deRMEmitDivModPair : DecidableEq RMEmitDivModPairQ :=
  deForRange (deSum deRMDivMod (deSum deRMDivMod (deSum deRMSetAdd (deSum deRMSetAdd deRMEmitEndPair))))

private abbrev ftRMEmitB10 : Fintype RMEmitB10Q :=
  have hIf : Fintype RMB10IfQ := ftSum inferInstance (ftSum ftRMSetAdd (ftSum inferInstance ftRMSetAdd))
  ftForRange (ftSum ftRMDivMod (ftSum ftRMDivMod (ftSum ftRMSetAdd (ftSum ftRMMul
    (ftSum ftRMAdd (ftSum (Fin.fintype _) (ftSum hIf ftRMEmitEndPair)))))))

private def deRMEmitB10 : DecidableEq RMEmitB10Q :=
  have hIf : DecidableEq RMB10IfQ := deSum inferInstance (deSum deRMSetAdd (deSum inferInstance deRMSetAdd))
  deForRange (deSum deRMDivMod (deSum deRMDivMod (deSum deRMSetAdd (deSum deRMMul
    (deSum deRMAdd (deSum inferInstance (deSum hIf deRMEmitEndPair)))))))

private abbrev ftRMEmitB11 : Fintype RMEmitB11Q :=
  ftForRange (ftSum ftRMSetAdd (ftSum ftRMDivMod (ftSum ftRMSetAdd ftRMEmitEndPair)))

private def deRMEmitB11 : DecidableEq RMEmitB11Q :=
  deForRange (deSum deRMSetAdd (deSum deRMDivMod (deSum deRMSetAdd deRMEmitEndPair)))

private abbrev ftRMEmitB12 : Fintype RMEmitB12Q :=
  have hCnt : Fintype RMB12CountQ :=
    ftSum (ftSetConst 10) (ftSum ftRMMul (ftSum ftRMSetAdd (ftSum (Fin.fintype _) ftRMSub)))
  have hTest : Fintype RMB12TestQ :=
    ftSum ftRMSetAdd (ftSum inferInstance (ftSum ftRMMul (Fin.fintype _)))
  have hStep : Fintype RMB12StepQ :=
    ftSum ftRMSub (ftSum inferInstance (ftSum inferInstance (ftSum ftRMMul (ftSum ftRMAdd
      (ftSum (ftSetConst 2) (ftSum ftRMDivMod (ftSum inferInstance (ftSum inferInstance hTest))))))))
  have hFin : Fintype RMB12FinQ :=
    ftSum ftRMSetAdd (ftSum inferInstance (ftSum ftRMDivMod (ftSum inferInstance (ftSum inferInstance
      (ftSum inferInstance (ftSum inferInstance (ftSum ftRMMul
        (ftSum ftRMSetAdd (ftSum ftRMMul (ftSum ftRMAdd ftRMAdd))))))))))
  have hWhile : Fintype RMB12WhileQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hStep))
  have hDec : Fintype RMB12DecodeQ :=
    ftSum (ftSetConst 1) (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftSum hTest (ftSum hWhile hFin)))))
  have hSrcNz : Fintype RMB12SrcNzQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum (ftSetConst 2)
      (ftSum ftRMDivMod (ftSum ftRMSetAdd inferInstance))))
  have hSrc : Fintype RMB12SrcQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hSrcNz))
  have hDstP : Fintype RMB12DstParentQ :=
    ftSum (ftSetConst 2) (ftSum ftRMDivMod (ftSum inferInstance (ftSum (Fin.fintype _)
      (ftSum ftRMMul (ftSum ftRMSetAdd (ftSum ftRMAdd (ftSum inferInstance ftRMAdd)))))))
  have hDstE : Fintype RMB12DstElseQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum (Fin.fintype _)
      (ftSum inferInstance (ftSum ftRMSetAdd (ftSum inferInstance hDstP)))))
  have hDstT : Fintype RMB12DstThenQ := ftSum ftRMSetAdd inferInstance
  have hDst : Fintype RMB12DstQ :=
    ftSum (ftSetConst 2) (ftSum ftRMDivMod (ftSum ftRMSetAdd (ftSum (Fin.fintype _)
      (ftSum inferInstance (ftSum inferInstance (ftSum hDstE (ftSum inferInstance hDstT)))))))
  ftSum hCnt (ftForRange (ftSum hDec (ftSum hSrc (ftSum hDst ftRMEmitEndPair))))

private def deRMEmitB12 : DecidableEq RMEmitB12Q :=
  have hCnt : DecidableEq RMB12CountQ :=
    deSum (deSetConst 10) (deSum deRMMul (deSum deRMSetAdd (deSum inferInstance deRMSub)))
  have hTest : DecidableEq RMB12TestQ :=
    deSum deRMSetAdd (deSum inferInstance (deSum deRMMul inferInstance))
  have hStep : DecidableEq RMB12StepQ :=
    deSum deRMSub (deSum inferInstance (deSum inferInstance (deSum deRMMul (deSum deRMAdd
      (deSum (deSetConst 2) (deSum deRMDivMod (deSum inferInstance (deSum inferInstance hTest))))))))
  have hFin : DecidableEq RMB12FinQ :=
    deSum deRMSetAdd (deSum inferInstance (deSum deRMDivMod (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum inferInstance (deSum deRMMul
        (deSum deRMSetAdd (deSum deRMMul (deSum deRMAdd deRMAdd))))))))))
  have hWhile : DecidableEq RMB12WhileQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance hStep))
  have hDec : DecidableEq RMB12DecodeQ :=
    deSum (deSetConst 1) (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum hTest (deSum hWhile hFin)))))
  have hSrcNz : DecidableEq RMB12SrcNzQ :=
    deSum inferInstance (deSum inferInstance (deSum (deSetConst 2)
      (deSum deRMDivMod (deSum deRMSetAdd inferInstance))))
  have hSrc : DecidableEq RMB12SrcQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance hSrcNz))
  have hDstP : DecidableEq RMB12DstParentQ :=
    deSum (deSetConst 2) (deSum deRMDivMod (deSum inferInstance (deSum inferInstance
      (deSum deRMMul (deSum deRMSetAdd (deSum deRMAdd (deSum inferInstance deRMAdd)))))))
  have hDstE : DecidableEq RMB12DstElseQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum deRMSetAdd (deSum inferInstance hDstP)))))
  have hDstT : DecidableEq RMB12DstThenQ := deSum deRMSetAdd inferInstance
  have hDst : DecidableEq RMB12DstQ :=
    deSum (deSetConst 2) (deSum deRMDivMod (deSum deRMSetAdd (deSum inferInstance
      (deSum inferInstance (deSum inferInstance (deSum hDstE (deSum inferInstance hDstT)))))))
  deSum hCnt (deForRange (deSum hDec (deSum hSrc (deSum hDst deRMEmitEndPair))))

private abbrev ftRMEmitB13 : Fintype RMEmitB13Q :=
  have hUNz : Fintype RMB13UNzQ := ftSum inferInstance (ftSum inferInstance ftRMSetAdd)
  have hU : Fintype RMB13UQ := ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hUNz))
  have hV : Fintype RMB13VQ :=
    ftSum inferInstance (ftSum (Fin.fintype _) (ftSum (Fin.fintype _)
      (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance ftRMSetAdd)))))
  ftSum (ftSum inferInstance (Fin.fintype _)) (ftForRange (ftSum hU (ftSum hV ftRMEmitEndPair)))

private def deRMEmitB13 : DecidableEq RMEmitB13Q :=
  have hUNz : DecidableEq RMB13UNzQ := deSum inferInstance (deSum inferInstance deRMSetAdd)
  have hU : DecidableEq RMB13UQ := deSum inferInstance (deSum inferInstance (deSum inferInstance hUNz))
  have hV : DecidableEq RMB13VQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum inferInstance (deSum inferInstance deRMSetAdd)))))
  deSum (deSum inferInstance inferInstance) (deForRange (deSum hU (deSum hV deRMEmitEndPair)))

private abbrev ftRMEmitAllEdges : Fintype RMEmitAllEdgesQ :=
  have hG0 : Fintype RMEmitG0Q := ftSum (ftSum ftRMEmitB0 ftRMEmitB1) (ftSum ftRMEmitB2 ftRMEmitB3)
  have hG1 : Fintype RMEmitG1Q :=
    ftSum (ftSum ftRMEmitDivModPair ftRMEmitDivModPair) (ftSum ftRMEmitDivModPair ftRMEmitDivModPair)
  have hG2 : Fintype RMEmitG2Q :=
    ftSum (ftSum ftRMEmitDivModPair ftRMEmitDivModPair) (ftSum ftRMEmitB10 ftRMEmitB11)
  have hG3 : Fintype RMEmitG3Q := ftSum ftRMEmitB12 ftRMEmitB13
  ftSum hG0 (ftSum (ftSum hG1 hG2) hG3)

private def deRMEmitAllEdges : DecidableEq RMEmitAllEdgesQ :=
  have hG0 : DecidableEq RMEmitG0Q := deSum (deSum deRMEmitB0 deRMEmitB1) (deSum deRMEmitB2 deRMEmitB3)
  have hG1 : DecidableEq RMEmitG1Q :=
    deSum (deSum deRMEmitDivModPair deRMEmitDivModPair) (deSum deRMEmitDivModPair deRMEmitDivModPair)
  have hG2 : DecidableEq RMEmitG2Q :=
    deSum (deSum deRMEmitDivModPair deRMEmitDivModPair) (deSum deRMEmitB10 deRMEmitB11)
  have hG3 : DecidableEq RMEmitG3Q := deSum deRMEmitB12 deRMEmitB13
  deSum hG0 (deSum (deSum hG1 hG2) hG3)

-- Circuit emitter Blocks 0–9 (`Branch8_CircuitEmitters`)
private abbrev ftBlkEmitXorHalf1 (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitXorHalf1 rO rA rB)) :=
  ftSum (Fin.fintype _) (ftSum ftRMEmitUnary (ftSum (Fin.fintype _) (ftSum ftRMEmitUnary
    (ftSum ftRMEmitUnary (ftSum (Fin.fintype _) (ftSum ftRMEmitUnary
      (ftSum inferInstance (Fin.fintype _))))))))

private def deBlkEmitXorHalf1 (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitXorHalf1 rO rA rB)) :=
  deSum inferInstance (deSum deRMEmitUnary (deSum inferInstance (deSum deRMEmitUnary
    (deSum deRMEmitUnary (deSum inferInstance (deSum deRMEmitUnary
      (deSum inferInstance inferInstance)))))))

private abbrev ftBlkEmitXorHalf2 (rO rB : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitXorHalf2 rO rB)) :=
  ftSum (Fin.fintype _) (ftSum ftRMEmitUnary (ftSum ftRMEmitUnary (ftSum inferInstance
    (ftSum (Fin.fintype _) (ftSum (Fin.fintype _) (ftSum ftRMEmitUnary
      (ftSum (Fin.fintype _) ftRMEmitUnary)))))))

private def deBlkEmitXorHalf2 (rO rB : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitXorHalf2 rO rB)) :=
  deSum inferInstance (deSum deRMEmitUnary (deSum deRMEmitUnary (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum deRMEmitUnary
      (deSum inferInstance deRMEmitUnary)))))))

private abbrev ftBlkEmitXorAt (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitXorAt rO rA rB)) :=
  ftSum (ftBlkEmitXorHalf1 rO rA rB) (ftBlkEmitXorHalf2 rO rB)

private def deBlkEmitXorAt (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitXorAt rO rA rB)) :=
  deSum (deBlkEmitXorHalf1 rO rA rB) (deBlkEmitXorHalf2 rO rB)

private abbrev ftBlkEmitEqAt (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitEqAt rO rA rB)) :=
  ftSum (ftBlkEmitXorAt rO rA rB) (ftSum inferInstance (ftSum (Fin.fintype _)
    (ftSum (Fin.fintype _) ftRMEmitUnary)))

private def deBlkEmitEqAt (rO rA rB : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitEqAt rO rA rB)) :=
  deSum (deBlkEmitXorAt rO rA rB) (deSum inferInstance (deSum inferInstance
    (deSum inferInstance deRMEmitUnary)))

private abbrev ftBlkEqTest (rRes rA rB : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEqTest rRes rA rB)) :=
  ftSum (Fin.fintype _) (ftSum (Fin.fintype _) (ftSum ftRMAdd
    (ftSum inferInstance (ftSum (ftSetConst 1) (ftSum inferInstance inferInstance)))))

private def deBlkEqTest (rRes rA rB : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEqTest rRes rA rB)) :=
  deSum inferInstance (deSum inferInstance (deSum deRMAdd
    (deSum inferInstance (deSum (deSetConst 1) (deSum inferInstance inferInstance)))))

private abbrev ftBlkCoeffPowY (rRes rM rP : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkCoeffPowY rRes rM rP)) :=
  ftSum inferInstance (ftSum ftRMAdd (ftSum ftRMAdd (ftSum ftRMDivMod
    (ftSum (ftBlkEqTest rRes Branch8CircuitEmit.s1 rP) (ftSum ftRMDivMod
      (ftSum ftRMAdd (ftSum ftRMAdd (ftSum (Fin.fintype _) (ftSum (Fin.fintype _)
        (ftSum ftRMAdd (ftSum inferInstance (ftSum (ftSetConst 1)
          (ftSum inferInstance inferInstance)))))))))))))

private def deBlkCoeffPowY (rRes rM rP : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkCoeffPowY rRes rM rP)) :=
  deSum inferInstance (deSum deRMAdd (deSum deRMAdd (deSum deRMDivMod
    (deSum (deBlkEqTest rRes Branch8CircuitEmit.s1 rP) (deSum deRMDivMod
      (deSum deRMAdd (deSum deRMAdd (deSum inferInstance (deSum inferInstance
        (deSum deRMAdd (deSum inferInstance (deSum (deSetConst 1)
          (deSum inferInstance inferInstance)))))))))))))

private abbrev ftBlkDftUnifiedMat (rW rS rSt rO : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkDftUnifiedMat rW rS rSt rO)) :=
  ftSum inferInstance (ftSum ftRMAdd (ftSum ftRMDivMod (ftSum ftRMDivMod
    (ftSum ftRMMul (ftSum ftRMAdd (ftSum ftRMMul (ftSum ftRMAdd (ftSum ftRMDivMod
      (ftSum ftRMMul (ftSum ftRMAdd (ftSum inferInstance
        (ftBlkCoeffPowY Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2))))))))))))

private def deBlkDftUnifiedMat (rW rS rSt rO : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkDftUnifiedMat rW rS rSt rO)) :=
  deSum inferInstance (deSum deRMAdd (deSum deRMDivMod (deSum deRMDivMod
    (deSum deRMMul (deSum deRMAdd (deSum deRMMul (deSum deRMAdd (deSum deRMDivMod
      (deSum deRMMul (deSum deRMAdd (deSum inferInstance
        (deBlkCoeffPowY Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2))))))))))))

private abbrev ftBlkRingMulActive : Fintype (BlockQ Branch8CircuitEmit.blkRingMulActive) :=
  ftSum ftRMDivMod (ftSum ftRMAdd (ftSum inferInstance
    (ftBlkCoeffPowY Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)))

private def deBlkRingMulActive : DecidableEq (BlockQ Branch8CircuitEmit.blkRingMulActive) :=
  deSum deRMDivMod (deSum deRMAdd (deSum inferInstance
    (deBlkCoeffPowY Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)))

private abbrev ftBlkEmitInitInputs : Fintype (BlockQ Branch8CircuitEmit.blkEmitInitInputs) :=
  ftForRange (ftSum (Fin.fintype _) ftRMEmitUnary)

private def deBlkEmitInitInputs : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitInitInputs) :=
  deForRange (deSum inferInstance deRMEmitUnary)

private abbrev ftBlkCountAllBase {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : Fintype Q) : Fintype (BlockQ (Branch8CircuitEmit.blkCountAllBase B)) :=
  ftSum inferInstance (ftSum (ftForRange (ftSum (Fin.fintype _)
    (ftForRange (ftSum hQ (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))))))
    inferInstance)

private def deBlkCountAllBase {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : DecidableEq Q) : DecidableEq (BlockQ (Branch8CircuitEmit.blkCountAllBase B)) :=
  deSum inferInstance (deSum (deForRange (deSum inferInstance
    (deForRange (deSum hQ (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))))
    inferInstance)

private abbrev ftBlkParityHitStep (useInOff : Bool) (rInOff : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkParityHitStep useInOff rInOff)) :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum ftRMAdd
    (ftSum (ftBlkEmitXorAt Branch8CircuitEmit.rCurWire Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)
      (Fin.fintype _)))))

private def deBlkParityHitStep (useInOff : Bool) (rInOff : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkParityHitStep useInOff rInOff)) :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum deRMAdd
    (deSum (deBlkEmitXorAt Branch8CircuitEmit.rCurWire Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)
      inferInstance))))

private abbrev ftBlkEmitParityRows {Q : Type} (useInOff : Bool)
    (rOutOff rInOff : Fin Branch8CircuitEmit.R_emit)
    (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q) (hQ : Fintype Q) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitParityRows useInOff rOutOff rInOff B)) :=
  ftSum inferInstance (ftForRange (ftSum (Fin.fintype _) (ftSum inferInstance
    (ftSum (ftForRange (ftSum hQ (ftSum inferInstance (ftSum inferInstance
      (ftSum inferInstance (ftBlkParityHitStep useInOff rInOff))))))
    (ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum inferInstance
      (ftSum (ftBlkEmitEqAt Branch8CircuitEmit.rCurWire Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)
        (Fin.fintype _))))))))))

private def deBlkEmitParityRows {Q : Type} (useInOff : Bool)
    (rOutOff rInOff : Fin Branch8CircuitEmit.R_emit)
    (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q) (hQ : DecidableEq Q) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitParityRows useInOff rOutOff rInOff B)) :=
  deSum inferInstance (deForRange (deSum inferInstance (deSum inferInstance
    (deSum (deForRange (deSum hQ (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deBlkParityHitStep useInOff rInOff))))))
    (deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum inferInstance
      (deSum (deBlkEmitEqAt Branch8CircuitEmit.rCurWire Branch8CircuitEmit.rWArg1 Branch8CircuitEmit.rWArg2)
        inferInstance)))))))))

private abbrev ftBlkEmitAllConjs {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : Fintype Q) : Fintype (BlockQ (Branch8CircuitEmit.blkEmitAllConjs B)) :=
  ftSum (Fin.fintype _) (ftSum inferInstance (ftForRange
    (ftSum (ftForRange (ftSum hQ (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))))
    (ftSum (Fin.fintype _) (ftSum inferInstance (ftSum ftRMAdd (ftSum (Fin.fintype _)
      (ftSum ftRMEmitUnary (ftSum ftRMEmitUnary inferInstance)))))))))

private def deBlkEmitAllConjs {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : DecidableEq Q) : DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitAllConjs B)) :=
  deSum inferInstance (deSum inferInstance (deForRange
    (deSum (deForRange (deSum hQ (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))
    (deSum inferInstance (deSum inferInstance (deSum deRMAdd (deSum inferInstance
      (deSum deRMEmitUnary (deSum deRMEmitUnary inferInstance)))))))))

private abbrev ftBlkEmitLinearMap {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : Fintype Q) : Fintype (BlockQ (Branch8CircuitEmit.blkEmitLinearMap B)) :=
  have hSetup : Fintype (BlockQ (Branch8CircuitEmit.blkEmitLinearSetup B)) :=
    ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum inferInstance (ftBlkCountAllBase B hQ))))
  have hBody : Fintype (BlockQ (Branch8CircuitEmit.blkEmitLinearBody B)) :=
    ftSum ftRMEmitUnary (ftSum inferInstance (ftSum inferInstance (ftSum ftRMAdd
      (ftSum ftRMEmitUnary (ftSum ftBlkEmitInitInputs
        (ftSum (ftBlkEmitParityRows false Branch8CircuitEmit.rNumIn Branch8CircuitEmit.rNumIn B hQ)
          (ftBlkEmitAllConjs B hQ)))))))
  ftSum hSetup hBody

private def deBlkEmitLinearMap {Q : Type} (B : Branch8CircuitEmit.RMBlock Branch8CircuitEmit.R_emit Q)
    (hQ : DecidableEq Q) : DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitLinearMap B)) :=
  have hSetup : DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitLinearSetup B)) :=
    deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum inferInstance (deBlkCountAllBase B hQ))))
  have hBody : DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitLinearBody B)) :=
    deSum deRMEmitUnary (deSum inferInstance (deSum inferInstance (deSum deRMAdd
      (deSum deRMEmitUnary (deSum deBlkEmitInitInputs
        (deSum (deBlkEmitParityRows false Branch8CircuitEmit.rNumIn Branch8CircuitEmit.rNumIn B hQ)
          (deBlkEmitAllConjs B hQ)))))))
  deSum hSetup hBody

private abbrev ftBlkEmitBilinearRingMul :
    Fintype (BlockQ Branch8CircuitEmit.blkEmitBilinearRingMul) :=
  have hPair : Fintype (BlockQ Branch8CircuitEmit.blkEmitPairConjs2J) :=
    ftForRange (ftForRange (ftSum inferInstance (ftSum ftRMAdd (ftSum (Fin.fintype _)
      (ftSum ftRMEmitUnary ftRMEmitUnary)))))
  have hSetup : Fintype (BlockQ Branch8CircuitEmit.blkEmitBilinearSetup) :=
    ftSum inferInstance (ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance
      (ftSum ftRMAdd (ftSum ftRMMul (ftSum inferInstance (ftSum ftRMAdd
        (ftBlkCountAllBase Branch8CircuitEmit.blkRingMulActive ftBlkRingMulActive))))))))
  have hBody : Fintype (BlockQ Branch8CircuitEmit.blkEmitBilinearBody) :=
    ftSum ftRMEmitUnary (ftSum inferInstance (ftSum inferInstance (ftSum ftRMAdd
      (ftSum ftRMEmitUnary (ftSum ftBlkEmitInitInputs (ftSum hPair
        (ftSum (ftBlkEmitParityRows true Branch8CircuitEmit.rNumIn Branch8CircuitEmit.rTotalIn
            Branch8CircuitEmit.blkRingMulActive ftBlkRingMulActive)
          (ftBlkEmitAllConjs Branch8CircuitEmit.blkRingMulActive ftBlkRingMulActive))))))))
  ftSum hSetup hBody

private def deBlkEmitBilinearRingMul :
    DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBilinearRingMul) :=
  have hPair : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitPairConjs2J) :=
    deForRange (deForRange (deSum inferInstance (deSum deRMAdd (deSum inferInstance
      (deSum deRMEmitUnary deRMEmitUnary)))))
  have hSetup : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBilinearSetup) :=
    deSum inferInstance (deSum inferInstance (deSum deRMAdd (deSum inferInstance
      (deSum deRMAdd (deSum deRMMul (deSum inferInstance (deSum deRMAdd
        (deBlkCountAllBase Branch8CircuitEmit.blkRingMulActive deBlkRingMulActive))))))))
  have hBody : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBilinearBody) :=
    deSum deRMEmitUnary (deSum inferInstance (deSum inferInstance (deSum deRMAdd
      (deSum deRMEmitUnary (deSum deBlkEmitInitInputs (deSum hPair
        (deSum (deBlkEmitParityRows true Branch8CircuitEmit.rNumIn Branch8CircuitEmit.rTotalIn
            Branch8CircuitEmit.blkRingMulActive deBlkRingMulActive)
          (deBlkEmitAllConjs Branch8CircuitEmit.blkRingMulActive deBlkRingMulActive))))))))
  deSum hSetup hBody

private abbrev ftBlkEmitBlock0 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock0) :=
  have hRead : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock0Read) :=
    ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum (Fin.fintype _) (Fin.fintype _))))
  have hBody : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock0Body) :=
    ftSum (Fin.fintype _) (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance hRead)))
  ftSum inferInstance (ftSum ftRMAdd (ftForRange hBody))

private def deBlkEmitBlock0 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock0) :=
  have hRead : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock0Read) :=
    deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum inferInstance inferInstance)))
  have hBody : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock0Body) :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance hRead)))
  deSum inferInstance (deSum deRMAdd (deForRange hBody))

private abbrev ftBlkEmitBlock1 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock1) :=
  ftSum inferInstance (ftSum ftRMAdd (ftForRange (Fin.fintype _)))

private def deBlkEmitBlock1 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock1) :=
  deSum inferInstance (deSum deRMAdd (deForRange inferInstance))

private abbrev ftBlkEmitBlock2 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock2) :=
  have hBody : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock2Body) :=
    ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum (Fin.fintype _) (Fin.fintype _))))
  ftForRange hBody

private def deBlkEmitBlock2 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock2) :=
  have hBody : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock2Body) :=
    deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum inferInstance inferInstance)))
  deForRange hBody

private abbrev ftBlkEmitBlock3 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock3) :=
  have hCntStep : Fintype (BlockQ Branch8CircuitEmit.blkCountFwdInStep) :=
    ftSum ftRMDivMod (ftSum ftRMDivMod (ftSum
      (ftBlkEqTest Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg2 Branch8CircuitEmit.rBlkIdx)
      (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance inferInstance)))))
  have hCnt : Fintype (BlockQ Branch8CircuitEmit.blkCountFwdIn) :=
    ftSum inferInstance (ftForRange hCntStep)
  have hStep : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock3Step) :=
    ftSum hCnt (ftSum inferInstance
      (ftBlkEmitLinearMap
        (Branch8CircuitEmit.blkDftUnifiedMat Branch8CircuitEmit.rWExp Branch8CircuitEmit.rJ
          Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)
        (ftBlkDftUnifiedMat Branch8CircuitEmit.rWExp Branch8CircuitEmit.rJ
          Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)))
  ftSum inferInstance (ftSum ftRMAdd (ftSum ftRMMul (ftForRange hStep)))

private def deBlkEmitBlock3 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock3) :=
  have hCntStep : DecidableEq (BlockQ Branch8CircuitEmit.blkCountFwdInStep) :=
    deSum deRMDivMod (deSum deRMDivMod (deSum
      (deBlkEqTest Branch8CircuitEmit.rMatHit Branch8CircuitEmit.rWArg2 Branch8CircuitEmit.rBlkIdx)
      (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))
  have hCnt : DecidableEq (BlockQ Branch8CircuitEmit.blkCountFwdIn) :=
    deSum inferInstance (deForRange hCntStep)
  have hStep : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock3Step) :=
    deSum hCnt (deSum inferInstance
      (deBlkEmitLinearMap
        (Branch8CircuitEmit.blkDftUnifiedMat Branch8CircuitEmit.rWExp Branch8CircuitEmit.rJ
          Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)
        (deBlkDftUnifiedMat Branch8CircuitEmit.rWExp Branch8CircuitEmit.rJ
          Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)))
  deSum inferInstance (deSum deRMAdd (deSum deRMMul (deForRange hStep)))

private abbrev ftBlkEmitSt2 (rW : Fin Branch8CircuitEmit.R_emit) :
    Fintype (BlockQ (Branch8CircuitEmit.blkEmitSt2 rW)) :=
  ftSum inferInstance (ftSum ftRMAdd (ftSum inferInstance (ftSum ftRMMul (ftSum inferInstance
    (ftForRange (ftBlkEmitLinearMap
      (Branch8CircuitEmit.blkDftUnifiedMat rW Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL1 Branch8CircuitEmit.rBlkAux2)
      (ftBlkDftUnifiedMat rW Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL1 Branch8CircuitEmit.rBlkAux2)))))))

private def deBlkEmitSt2 (rW : Fin Branch8CircuitEmit.R_emit) :
    DecidableEq (BlockQ (Branch8CircuitEmit.blkEmitSt2 rW)) :=
  deSum inferInstance (deSum deRMAdd (deSum inferInstance (deSum deRMMul (deSum inferInstance
    (deForRange (deBlkEmitLinearMap
      (Branch8CircuitEmit.blkDftUnifiedMat rW Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL1 Branch8CircuitEmit.rBlkAux2)
      (deBlkDftUnifiedMat rW Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL1 Branch8CircuitEmit.rBlkAux2)))))))

private abbrev ftBlkEmitBlock7 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock7) :=
  ftSum inferInstance (ftSum ftRMAdd (ftForRange ftBlkEmitBilinearRingMul))

private def deBlkEmitBlock7 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock7) :=
  deSum inferInstance (deSum deRMAdd (deForRange deBlkEmitBilinearRingMul))

private abbrev ftBlkEmitBlock8 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlock8) :=
  ftSum inferInstance (ftSum ftRMAdd (ftSum ftRMMul (ftSum inferInstance
    (ftForRange (ftBlkEmitLinearMap
      (Branch8CircuitEmit.blkDftUnifiedMat Branch8CircuitEmit.rInvWExp Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)
      (ftBlkDftUnifiedMat Branch8CircuitEmit.rInvWExp Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx))))))

private def deBlkEmitBlock8 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlock8) :=
  deSum inferInstance (deSum deRMAdd (deSum deRMMul (deSum inferInstance
    (deForRange (deBlkEmitLinearMap
      (Branch8CircuitEmit.blkDftUnifiedMat Branch8CircuitEmit.rInvWExp Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx)
      (deBlkDftUnifiedMat Branch8CircuitEmit.rInvWExp Branch8CircuitEmit.rBlkAux1
        Branch8CircuitEmit.rL2 Branch8CircuitEmit.rBlkIdx))))))

/-- Explicit `Fintype` witness for `RMEmitBlocks0to9Q`. -/
abbrev fintypeRMEmitBlocks0to9Q : Fintype RMEmitBlocks0to9Q :=
  have h04 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlocks0to4) :=
    ftSum ftBlkEmitBlock0 (ftSum ftBlkEmitBlock1 (ftSum ftBlkEmitBlock2
      (ftSum ftBlkEmitBlock3 (ftBlkEmitSt2 Branch8CircuitEmit.rWExp))))
  have h59 : Fintype (BlockQ Branch8CircuitEmit.blkEmitBlocks5to9) :=
    ftSum ftBlkEmitBlock3 (ftSum (ftBlkEmitSt2 Branch8CircuitEmit.rWExp)
      (ftSum ftBlkEmitBlock7 (ftSum ftBlkEmitBlock8 (ftBlkEmitSt2 Branch8CircuitEmit.rInvWExp))))
  ftSum h04 h59

/-- Explicit `DecidableEq` witness for `RMEmitBlocks0to9Q`. -/
def decEqRMEmitBlocks0to9Q : DecidableEq RMEmitBlocks0to9Q :=
  have h04 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlocks0to4) :=
    deSum deBlkEmitBlock0 (deSum deBlkEmitBlock1 (deSum deBlkEmitBlock2
      (deSum deBlkEmitBlock3 (deBlkEmitSt2 Branch8CircuitEmit.rWExp))))
  have h59 : DecidableEq (BlockQ Branch8CircuitEmit.blkEmitBlocks5to9) :=
    deSum deBlkEmitBlock3 (deSum (deBlkEmitSt2 Branch8CircuitEmit.rWExp)
      (deSum deBlkEmitBlock7 (deSum deBlkEmitBlock8 (deBlkEmitSt2 Branch8CircuitEmit.rInvWExp))))
  deSum h04 h59

/-- Explicit `Fintype` witness for `RMMnetCoreQ`. -/
abbrev fintypeRMMnetCoreQ : Fintype RMMnetCoreQ :=
  ftSum ftRMComputeParams
    (ftSum (ftSum ftRMEmitUnary ftRMEmitUnary)
      (ftSum ftRMEmitAllEdges
        (ftSum (Fin.fintype 16)
          (ftSum fintypeRMEmitBlocks0to9Q Branch8bTail.fintypeRMEmitBlocks10to18Q))))

/-- Explicit `DecidableEq` witness for `RMMnetCoreQ`. -/
def decEqRMMnetCoreQ : DecidableEq RMMnetCoreQ :=
  deSum deRMComputeParams
    (deSum (deSum deRMEmitUnary deRMEmitUnary)
      (deSum deRMEmitAllEdges
        (deSum inferInstance
          (deSum decEqRMEmitBlocks0to9Q Branch8bTail.decEqRMEmitBlocks10to18Q))))

/-- Explicit `Fintype` witness for `RMMnetExactQ`. -/
abbrev fintypeRMMnetExactQ : Fintype RMMnetExactQ :=
  ftSum (ftSum ftRMParseInputStd inferInstance) fintypeRMMnetCoreQ

/-- Explicit `DecidableEq` witness for `RMMnetExactQ`. -/
def decEqRMMnetExactQ : DecidableEq RMMnetExactQ :=
  deSum (deSum deRMParseInputStd inferInstance) decEqRMMnetCoreQ

/-- Explicit `Fintype` witness for `RMMnetLeQ`. -/
abbrev fintypeRMMnetLeQ : Fintype RMMnetLeQ :=
  fintypeRMMnetExactQ

/-- Explicit `DecidableEq` witness for `RMMnetLeQ`. -/
def decEqRMMnetLeQ : DecidableEq RMMnetLeQ :=
  decEqRMMnetExactQ

/-- Explicit `Fintype` witness for `RMMnetSepQ`. -/
abbrev fintypeRMMnetSepQ : Fintype RMMnetSepQ :=
  ftSum ftRMParseInputSep fintypeRMMnetCoreQ

/-- Explicit `DecidableEq` witness for `RMMnetSepQ`. -/
def decEqRMMnetSepQ : DecidableEq RMMnetSepQ :=
  deSum deRMParseInputSep decEqRMMnetCoreQ

end GlueMnetRMProg
