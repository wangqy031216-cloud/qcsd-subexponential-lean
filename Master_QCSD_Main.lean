import Branch1_Recovery
import Glue_NetworkAndConv
import Glue_MnetRMProg
import Branch4_Phase1Dev

open QCSD.Defs

private lemma padW_bound_pow_n {C_W d_W W n : ℕ} (hn : 1 ≤ n) (hW : W ≤ C_W * (n + 1) ^ d_W) :
    W ≤ (C_W * 2 ^ d_W) * n ^ d_W := by
  have h1 : (n + 1) ^ d_W ≤ (2 * n) ^ d_W := Nat.pow_le_pow_left (by omega) d_W
  have h2 : (2 * n) ^ d_W = 2 ^ d_W * n ^ d_W := Nat.mul_pow 2 n d_W
  calc
    W ≤ C_W * (n + 1) ^ d_W := hW
    _ ≤ C_W * (2 ^ d_W * n ^ d_W) := Nat.mul_le_mul_left C_W (h2 ▸ h1)
    _ = (C_W * 2 ^ d_W) * n ^ d_W := (Nat.mul_assoc C_W (2 ^ d_W) (n ^ d_W)).symm

private lemma countPrefix_eq_filter_card {n : ℕ}
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (pre : List Bool) :
    Branch5PadAndSep.prefixCountGen sols pre =
      (sols.filter (fun q =>
        (((List.ofFn fun i => decide (q.1 i = 1)) ++
          (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card := by
  classical
  unfold Branch5PadAndSep.prefixCountGen Branch5PadAndSep.prefixSolsGen
  congr 1
  ext q
  simp only [Finset.mem_filter, Branch5PadAndSep.QCSD_encodeSolPair, QCSD_vecToBits, List.ofFn_eq_map]
  exact Finset.mem_filter

theorem qcsd_exact_master
    (hTC : QCSD.Defs.QCSD_TC10) :
    ∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstance
        (fun (inp : QCSD.Defs.QCSD_Instance) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_Correct inp o)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n) := by
  let _ : Fintype GlueMnetRMProg.RMMnetExactQ := GlueMnetRMProg.fintypeRMMnetExactQ
  let _ : DecidableEq GlueMnetRMProg.RMMnetExactQ := GlueMnetRMProg.decEqRMMnetExactQ
  obtain ⟨M_tm, Ctm, kst, C_W, d_W, padW, hCtm, hM⟩ :=
    Branch4Phase1Dev.compileRMProg_std_spec GlueMnetRMProg.R_mnet
      GlueMnetRMProg.rmMnetExact GlueMnetRMProg.rmMnetExactEntry
      GlueMnetRMProg.mnetCV 2 GlueMnetRMProg.mnetCT 4 GlueMnetRMProg.mnetCT 4
      (fun x pre => GlueMnetRMProg.mnetMiddleStream 0 x.n x.h x.s x.t 0 pre)
      (fun x pre hn ht hpre => by
        obtain ⟨reg₁, hex⟩ := GlueMnetRMProg.rmMnetExact_spec x pre (by omega) ht hpre
        exact ⟨GlueMnetRMProg.rmMnetExactExit, reg₁,
          hex.weaken
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))⟩)
      (fun x pre hn ht hpre => by
        obtain ⟨_, hex⟩ := GlueMnetRMProg.rmMnetExact_spec x pre (by omega) ht hpre
        exact (GlueMnetRMProg.rmExec_emitted_length_le hex).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)))
  set C_pad := C_W * 2 ^ d_W
  refine qcsd_tc_recover_exact_v2 hTC
    Branch3.tcCDelta (max 1 d_W) (Branch3.tcKm + C_pad)
    (max 5 d_W) (Branch3.tcKcost + 7 * C_pad) 2 Branch3.tcKpred
    (GlueNetConv.padNet_tcAdmissible_simp C_pad d_W)
    M_tm Ctm hCtm kst 420 (by omega)
    (fun x pre => Branch5PadAndSep.padNet (padW x pre) (Branch3.N_exact x pre))
    (fun x ⟨hn, ht⟩ pre hpre => ?_)
  obtain ⟨hpad, k, hk, hst, htp, hsp⟩ := hM x pre hn ht hpre
  refine ⟨⟨k, hk, hst, ?_, hsp⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [htp, GlueMnetRMProg.encodeNet2_padNet_N_exact_eq_mnetWrap, List.append_assoc]
  · exact GlueNetConv.padNet_N_exact_tcClass2 x pre (by omega)
      (padW_bound_pow_n (by omega) hpad)
  · exact GlueNetConv.padNet_N_exact_edgeCount_bounds (padW x pre) x pre (by omega)
  · rw [GlueNetConv.padNet_N_exact_contraction (padW x pre) x pre hpre]
    exact countPrefix_eq_filter_card (QCSD_solutions x) pre

theorem qcsd_sep_master
    (hTC : QCSD.Defs.QCSD_TC10) :
    ∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstanceSep
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          2 ≤ inp.n ∧ inp.t₀ ≤ inp.n ∧ inp.t₁ ≤ inp.n)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_CorrectSep inp o)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n) := by
  let _ : Fintype GlueMnetRMProg.RMMnetSepQ := GlueMnetRMProg.fintypeRMMnetSepQ
  let _ : DecidableEq GlueMnetRMProg.RMMnetSepQ := GlueMnetRMProg.decEqRMMnetSepQ
  obtain ⟨M_tm, Ctm, kst, C_W, d_W, padW, hCtm, hM⟩ :=
    Branch4Phase1Dev.compileRMProg_sep_spec GlueMnetRMProg.R_mnet
      GlueMnetRMProg.rmMnetSep GlueMnetRMProg.rmMnetSepEntry
      GlueMnetRMProg.mnetCV 2 GlueMnetRMProg.mnetCT 4 GlueMnetRMProg.mnetCT 4
      (fun x pre => GlueMnetRMProg.mnetMiddleStream 2 x.n x.h x.s x.t₀ x.t₁ pre)
      (fun x pre hn ht0 ht1 hpre => by
        obtain ⟨reg₁, hex⟩ := GlueMnetRMProg.rmMnetSep_spec x pre (by omega) ht0 ht1 hpre
        exact ⟨GlueMnetRMProg.rmMnetSepExit, reg₁,
          hex.weaken
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))⟩)
      (fun x pre hn ht0 ht1 hpre => by
        obtain ⟨_, hex⟩ := GlueMnetRMProg.rmMnetSep_spec x pre (by omega) ht0 ht1 hpre
        exact (GlueMnetRMProg.rmExec_emitted_length_le hex).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)))
  set C_pad := C_W * 2 ^ d_W
  refine qcsd_tc_recover_sep_v2 hTC
    Branch3.tcCDelta (max 1 d_W) (Branch3.tcKm + C_pad)
    (max 5 d_W) (Branch3.tcKcost + 7 * C_pad) 2 Branch3.tcKpred
    (GlueNetConv.padNet_tcAdmissible_simp C_pad d_W)
    M_tm Ctm hCtm kst 420 (by omega)
    (fun x pre => Branch5PadAndSep.padNet (padW x pre) (Branch3.N_sep x pre))
    (fun x ⟨hn, ht0, ht1⟩ pre hpre => ?_)
  obtain ⟨hpad, k, hk, hst, htp, hsp⟩ := hM x pre hn ht0 ht1 hpre
  refine ⟨⟨k, hk, hst, ?_, hsp⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [htp, GlueMnetRMProg.encodeNet2_padNet_N_sep_eq_mnetWrap, List.append_assoc]
  · exact GlueNetConv.padNet_N_sep_tcClass2 x pre (by omega)
      (padW_bound_pow_n (by omega) hpad)
  · exact GlueNetConv.padNet_N_sep_edgeCount_bounds (padW x pre) x pre (by omega)
  · rw [GlueNetConv.padNet_N_sep_contraction (padW x pre) x pre hpre]
    exact countPrefix_eq_filter_card (QCSD_solutionsSep x) pre

theorem qcsd_le_master
    (hTC : QCSD.Defs.QCSD_TC10) :
    ∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstance
        (fun (inp : QCSD.Defs.QCSD_Instance) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_CorrectLe inp o)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n) := by
  let _ : Fintype GlueMnetRMProg.RMMnetLeQ := GlueMnetRMProg.fintypeRMMnetLeQ
  let _ : DecidableEq GlueMnetRMProg.RMMnetLeQ := GlueMnetRMProg.decEqRMMnetLeQ
  obtain ⟨M_tm, Ctm, kst, C_W, d_W, padW, hCtm, hM⟩ :=
    Branch4Phase1Dev.compileRMProg_std_spec GlueMnetRMProg.R_mnet
      GlueMnetRMProg.rmMnetLe GlueMnetRMProg.rmMnetLeEntry
      GlueMnetRMProg.mnetCV 2 GlueMnetRMProg.mnetCT 4 GlueMnetRMProg.mnetCT 4
      (fun x pre => GlueMnetRMProg.mnetMiddleStream 1 x.n x.h x.s x.t 0 pre)
      (fun x pre hn ht hpre => by
        obtain ⟨reg₁, hex⟩ := GlueMnetRMProg.rmMnetLe_spec x pre (by omega) ht hpre
        exact ⟨GlueMnetRMProg.rmMnetLeExit, reg₁,
          hex.weaken
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))⟩)
      (fun x pre hn ht hpre => by
        obtain ⟨_, hex⟩ := GlueMnetRMProg.rmMnetLe_spec x pre (by omega) ht hpre
        exact (GlueMnetRMProg.rmExec_emitted_length_le hex).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)))
  set C_pad := C_W * 2 ^ d_W
  refine qcsd_tc_recover_le_v2 hTC
    Branch3.tcCDelta (max 1 d_W) (Branch3.tcKm + C_pad)
    (max 5 d_W) (Branch3.tcKcost + 7 * C_pad) 2 Branch3.tcKpred
    (GlueNetConv.padNet_tcAdmissible_simp C_pad d_W)
    M_tm Ctm hCtm kst 420 (by omega)
    (fun x pre => Branch5PadAndSep.padNet (padW x pre) (Branch3.N_le x pre))
    (fun x ⟨hn, ht⟩ pre hpre => ?_)
  obtain ⟨hpad, k, hk, hst, htp, hsp⟩ := hM x pre hn ht hpre
  refine ⟨⟨k, hk, hst, ?_, hsp⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [htp, GlueMnetRMProg.encodeNet2_padNet_N_le_eq_mnetWrap, List.append_assoc]
  · exact GlueNetConv.padNet_N_le_tcClass2 x pre (by omega)
      (padW_bound_pow_n (by omega) hpad)
  · exact GlueNetConv.padNet_N_le_edgeCount_bounds (padW x pre) x pre (by omega)
  · rw [GlueNetConv.padNet_N_le_contraction (padW x pre) x pre hpre]
    exact countPrefix_eq_filter_card (QCSD_solutionsLe x) pre

theorem QCSD_main
    (hTC : QCSD.Defs.QCSD_TC10) :
    (∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstance
        (fun (inp : QCSD.Defs.QCSD_Instance) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_Correct inp o)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n)) ∧
    (∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstanceSep
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          2 ≤ inp.n ∧ inp.t₀ ≤ inp.n ∧ inp.t₁ ≤ inp.n)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_CorrectSep inp o)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_InstanceSep) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n)) ∧
    (∃ (A : QCSD.Defs.QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD.Defs.QCSD_ComputesOnEncoded3 A
        QCSD.Defs.QCSD_encodeInstance
        (fun (inp : QCSD.Defs.QCSD_Instance) (l : List Bool) =>
          QCSD.Defs.QCSD_decodeOutputN2 inp.n l)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance)
             (o : ℕ × Option (List Bool)) =>
          QCSD.Defs.QCSD_CorrectLe inp o)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_timeBound Ct inp.n)
        (fun (inp : QCSD.Defs.QCSD_Instance) =>
          QCSD.Defs.QCSD_spaceBound ksp inp.n)) :=
  ⟨qcsd_exact_master hTC, qcsd_sep_master hTC, qcsd_le_master hTC⟩

