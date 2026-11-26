import Branch2_Algebra

namespace GlueTwoLayerConv

open Branch2Algebra
open QCSD.Defs

/-!
# Exact Definitions Matching `Branch3_Network.lean`
-/

def paramOmegaExp (d : ℕ) : ℕ := 3 ^ (paramK d + 1 - paramEll d)
def paramInvOmegaExp (d : ℕ) : ℕ := 3 * paramJ d - paramOmegaExp d

def linearMapTarget (numIn : ℕ) (mat : ℕ → ℕ → Bool) (inp : ℕ → Bool) (j : ℕ) : Bool :=
  ((List.range numIn).filter (fun i => mat j i)).foldl (fun b i => bne b (inp i)) false

def bilinearMapTarget (n1 n2 : ℕ) (tensor : ℕ → ℕ → ℕ → Bool) (inp : ℕ → Bool) (j : ℕ) : Bool :=
  ((List.range (n1 * n2)).filter (fun k => tensor j (k / n2) (k % n2))).foldl
    (fun b k => bne b (inp (k / n2) && inp (n1 + k % n2))) false

def coeffPowY (J m p : ℕ) : Bool :=
  decide (m % (3 * J) = p ∨ m % (3 * J) = 2 * J + p % J)

def ringMulTensor (J : ℕ) (p t1 t2 : ℕ) : Bool :=
  coeffPowY J (t1 + t2) p

def ringMulBits (J : ℕ) (u v : ℕ → Bool) (p : ℕ) : Bool :=
  bilinearMapTarget (2 * J) (2 * J) (ringMulTensor J)
    (fun idx => if idx < 2 * J then u idx else v (idx - 2 * J)) p

def fwdSt1InIndices (n J L2 j2 : ℕ) : List ℕ :=
  (List.range n).filter (fun idx => decide ((idx / J) % L2 = j2))

def fwdSt1Mat (J L1 wExp : ℕ) (inIndices : List ℕ) (outIdx inK : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let idx := inIndices.getD inK 0
  let r := idx / J
  let u := idx % J
  decide (q1 < L1) && coeffPowY J (wExp * r * q1 + u) p

def fullSt1Mat (J L1 L2 wExp j2 : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j1 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  let r := L2 * j1 + j2
  decide (q1 < L1 ∧ j1 < L1) && coeffPowY J (wExp * r * q1 + t) p

def st2Mat (J L1 L2 wExp : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q2 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j2 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  decide (q2 < L2 ∧ j2 < L2) && coeffPowY J (wExp * L1 * j2 * q2 + t) p

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

def twoLayerCycMul (n : ℕ) (a b : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i =>
    let aB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (a ⟨idx, h⟩) else false
    let bB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (b ⟨idx, h⟩) else false
    boolToZMod2 (bne (twoLayerPolyMulBit n aB bB i.val)
                     (twoLayerPolyMulBit n aB bB (i.val + n)))

def TwoLayerConvSpec (n : ℕ) : Prop :=
  ∀ (a b : Fin n → ZMod 2) (i : Fin n),
    twoLayerCycMul n a b i = QCSD_cycMul n a b i

/-!
# Section 1: Parameter, `Bool`, `List.foldl bne`, and `coeffPowY` Bridges
-/

lemma boolToZMod2_bne (a b : Bool) :
    boolToZMod2 (bne a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

@[simp] lemma boolToZMod2_false : boolToZMod2 false = 0 := rfl
@[simp] lemma boolToZMod2_true : boolToZMod2 true = 1 := rfl

lemma paramOmegaExp_mul_paramL {d : ℕ} (hd : 1 ≤ d) :
    paramOmegaExp d * paramL d = 3 * paramJ d := by
  have hle : paramEll d ≤ paramK d + 1 := paramEll_le_paramK_succ hd
  unfold paramOmegaExp paramL paramJ
  rw [← pow_add, Nat.sub_add_cancel hle, pow_succ']

lemma paramOmegaExp_eq_div {d : ℕ} (hd : 1 ≤ d) :
    paramOmegaExp d = 3 * paramJ d / paramL d := by
  have hL : 0 < paramL d := one_le_paramL d
  rw [← paramOmegaExp_mul_paramL hd, Nat.mul_div_cancel _ hL]

lemma paramInvOmegaExp_eq {d : ℕ} (hd : 1 ≤ d) :
    paramInvOmegaExp d = (3 * paramJ d / paramL d) * (paramL d - 1) := by
  calc
    paramInvOmegaExp d = 3 * paramJ d - paramOmegaExp d := rfl
    _ = paramOmegaExp d * paramL d - paramOmegaExp d * 1 := by
      rw [← paramOmegaExp_mul_paramL hd, mul_one]
    _ = paramOmegaExp d * (paramL d - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
    _ = (3 * paramJ d / paramL d) * (paramL d - 1) := by rw [paramOmegaExp_eq_div hd]

/-- Bridge between `coeffPowY` and `monomialModVec`. -/
lemma boolToZMod2_coeffPowY {J : ℕ} (hJ : 0 < J) (m : ℕ) (p : Fin (2 * J)) :
    boolToZMod2 (coeffPowY J m p.val) = monomialModVec J m p := by
  unfold coeffPowY monomialModVec
  set r := m % (3 * J)
  have hr_lt : r < 3 * J := Nat.mod_lt m (by omega)
  have hp_lt : p.val < 2 * J := p.isLt
  have hmod_lt : p.val % J < J := Nat.mod_lt p.val hJ
  by_cases hr2 : r < 2 * J
  · have hnot_ge : ¬ (2 * J ≤ r) := by omega
    have hnot_or2 : r ≠ 2 * J + p.val % J := by omega
    simp only [hnot_ge, false_and, ↓reduceIte, add_zero, hnot_or2, or_false]
    by_cases hrp : r = p.val <;> simp [hrp]
  · have hge : 2 * J ≤ r := by omega
    have hr_ne_p : r ≠ p.val := by omega
    simp only [hr_ne_p, false_or, ↓reduceIte, zero_add, hge, true_and]
    by_cases hpJ : p.val < J
    · have hp_mod : p.val % J = p.val := Nat.mod_eq_of_lt hpJ
      have hne_rJ : r - J ≠ p.val := by omega
      rw [hp_mod]
      simp only [hne_rJ, ↓reduceIte, add_zero]
      by_cases hsub : r - 2 * J = p.val
      · have hreq : r = 2 * J + p.val := by omega
        simp only [hsub, ↓reduceIte]
        simp [hreq]
      · have hrne : r ≠ 2 * J + p.val := by omega
        simp [hsub, hrne]
    · have hp_ge : J ≤ p.val := by omega
      have hp_mod : p.val % J = p.val - J := by
        have hrew : p.val = (p.val - J) + 1 * J := by omega
        conv_lhs => rw [hrew]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hne_r2J : r - 2 * J ≠ p.val := by omega
      rw [hp_mod]
      simp only [hne_r2J, ↓reduceIte, zero_add]
      by_cases hsub : r - J = p.val
      · have hreq : r = 2 * J + (p.val - J) := by omega
        simp only [hsub, ↓reduceIte]
        simp [hreq]
      · have hrne : r ≠ 2 * J + (p.val - J) := by omega
        simp [hsub, hrne]

lemma boolToZMod2_foldl_bne {α : Type*} :
    ∀ (l : List α) (f : α → Bool) (init : Bool),
      boolToZMod2 (l.foldl (fun b a => bne b (f a)) init) =
        boolToZMod2 init + (l.map (fun a => boolToZMod2 (f a))).sum
  | [], _, init => by simp
  | a :: ls, f, init => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [boolToZMod2_foldl_bne ls f (bne init (f a)), boolToZMod2_bne, add_assoc]

lemma map_filter_sum_zmod2 {α : Type*} :
    ∀ (l : List α) (pred : α → Bool) (f : α → ZMod 2),
      ((l.filter pred).map f).sum =
        (l.map (fun a => boolToZMod2 (pred a) * f a)).sum
  | [], _, _ => by simp
  | a :: ls, pred, f => by
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hp : pred a
    · simp [map_filter_sum_zmod2 ls pred f]
    · simp [map_filter_sum_zmod2 ls pred f]

lemma list_range_map_sum_eq_fin_sum {R : Type*} [AddCommMonoid R] :
    ∀ (M : ℕ) (g : ℕ → R),
      ((List.range M).map g).sum = Finset.univ.sum (fun i : Fin M => g i.val)
  | 0, _ => by simp
  | M + 1, g => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      list_range_map_sum_eq_fin_sum M g, Fin.sum_univ_castSucc]
    rfl

lemma fin_length_getD_sum_eq_list_map_sum {R : Type*} [AddCommMonoid R] :
    ∀ (l : List ℕ) (g : ℕ → R),
      Finset.univ.sum (fun k : Fin l.length => g (l.getD k.val 0)) = (l.map g).sum
  | [], _ => by simp
  | a :: ls, g => by
    rw [List.map_cons, List.sum_cons]
    exact (Fin.sum_univ_succ (fun k : Fin (ls.length + 1) => g ((a :: ls).getD k.val 0))).trans
      (congrArg (g a + ·) (fin_length_getD_sum_eq_list_map_sum ls g))

lemma boolToZMod2_linearMapTarget (numIn : ℕ) (mat : ℕ → ℕ → Bool)
    (inp : ℕ → Bool) (j : ℕ) :
    boolToZMod2 (linearMapTarget numIn mat inp j) =
      Finset.univ.sum (fun i : Fin numIn =>
        boolToZMod2 (mat j i.val) * boolToZMod2 (inp i.val)) := by
  unfold linearMapTarget
  rw [boolToZMod2_foldl_bne, boolToZMod2_false, zero_add, map_filter_sum_zmod2,
    list_range_map_sum_eq_fin_sum]

lemma boolToZMod2_bilinearMapTarget (n1 n2 : ℕ) (hn2 : 0 < n2)
    (tensor : ℕ → ℕ → ℕ → Bool) (inp : ℕ → Bool) (j : ℕ) :
    boolToZMod2 (bilinearMapTarget n1 n2 tensor inp j) =
      Finset.univ.sum (fun t1 : Fin n1 =>
        Finset.univ.sum (fun t2 : Fin n2 =>
          boolToZMod2 (tensor j t1.val t2.val) *
            (boolToZMod2 (inp t1.val) * boolToZMod2 (inp (n1 + t2.val))))) := by
  unfold bilinearMapTarget
  rw [boolToZMod2_foldl_bne, boolToZMod2_false, zero_add, map_filter_sum_zmod2,
    list_range_map_sum_eq_fin_sum]
  let e : Fin n1 × Fin n2 ≃ Fin (n1 * n2) :=
    { toFun := fun ⟨t1, t2⟩ =>
        ⟨t1.val * n2 + t2.val, by
          have h1 : t1.val + 1 ≤ n1 := t1.isLt
          have h2 : t2.val < n2 := t2.isLt
          calc
            t1.val * n2 + t2.val < (t1.val + 1) * n2 := by rw [add_mul, one_mul]; omega
            _ ≤ n1 * n2 := Nat.mul_le_mul_right n2 h1⟩
      invFun := fun k =>
        (⟨k.val / n2, Nat.div_lt_of_lt_mul (Nat.mul_comm n1 n2 ▸ k.isLt)⟩,
         ⟨k.val % n2, Nat.mod_lt _ hn2⟩)
      left_inv := fun ⟨t1, t2⟩ => by
        have h2 : t2.val < n2 := t2.isLt
        have hdiv : (t1.val * n2 + t2.val) / n2 = t1.val := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn2, Nat.div_eq_of_lt h2, zero_add]
        have hmod : (t1.val * n2 + t2.val) % n2 = t2.val := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
        ext <;> simp [hdiv, hmod]
      right_inv := fun k => by
        ext
        dsimp only
        rw [Nat.mul_comm, Nat.div_add_mod] }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t1 _ => ?_)
  refine Finset.sum_congr rfl (fun t2 _ => ?_)
  have h2 : t2.val < n2 := t2.isLt
  have hdiv : (e (t1, t2)).val / n2 = t1.val := by
    dsimp [e]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn2, Nat.div_eq_of_lt h2, zero_add]
  have hmod : (e (t1, t2)).val % n2 = t2.val := by
    dsimp [e]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [hdiv, hmod, boolToZMod2_and]

/-!
# Section 2: Stage-by-Stage Equivalence with `Branch2Algebra`
-/

/-- Helper bijection `(idx : Fin (B * M)) ≃ Fin M × Fin B` via `(idx / B, idx % B)`. -/
def blockSplitEquiv (B M : ℕ) (hB : 0 < B) : (Fin M × Fin B) ≃ Fin (B * M) where
  toFun := fun ⟨j, t⟩ =>
    ⟨j.val * B + t.val, by
      have hj : j.val + 1 ≤ M := j.isLt
      have ht : t.val < B := t.isLt
      calc
        j.val * B + t.val < (j.val + 1) * B := by rw [add_mul, one_mul]; omega
        _ ≤ M * B := Nat.mul_le_mul_right B hj
        _ = B * M := Nat.mul_comm M B⟩
  invFun := fun k =>
    (⟨k.val / B, Nat.div_lt_of_lt_mul k.isLt⟩,
     ⟨k.val % B, Nat.mod_lt _ hB⟩)
  left_inv := fun ⟨j, t⟩ => by
    have ht : t.val < B := t.isLt
    have hdiv : (j.val * B + t.val) / B = j.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ht, zero_add]
    have hmod : (j.val * B + t.val) % B = t.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    ext <;> simp [hdiv, hmod]
  right_inv := fun k => by
    ext
    dsimp only
    rw [Nat.mul_comm, Nat.div_add_mod]

@[simp] lemma blockSplitEquiv_div (B M : ℕ) (hB : 0 < B) (j : Fin M) (t : Fin B) :
    (blockSplitEquiv B M hB (j, t)).val / B = j.val := by
  have ht : t.val < B := t.isLt
  dsimp [blockSplitEquiv]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ht, zero_add]

@[simp] lemma blockSplitEquiv_mod (B M : ℕ) (hB : 0 < B) (j : Fin M) (t : Fin B) :
    (blockSplitEquiv B M hB (j, t)).val % B = t.val := by
  have ht : t.val < B := t.isLt
  dsimp [blockSplitEquiv]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

def twoMulEquiv (J : ℕ) (hJ : 0 < J) : (Fin 2 × Fin J) ≃ Fin (2 * J) where
  toFun := fun ⟨b, u⟩ =>
    ⟨b.val * J + u.val, by
      have hb : b.val + 1 ≤ 2 := b.isLt
      have hu : u.val < J := u.isLt
      calc
        b.val * J + u.val < (b.val + 1) * J := by rw [add_mul, one_mul]; omega
        _ ≤ 2 * J := Nat.mul_le_mul_right J hb⟩
  invFun := fun k =>
    (⟨k.val / J, Nat.div_lt_of_lt_mul (Nat.mul_comm 2 J ▸ k.isLt)⟩,
     ⟨k.val % J, Nat.mod_lt _ hJ⟩)
  left_inv := fun ⟨b, u⟩ => by
    have hu : u.val < J := u.isLt
    have hdiv : (b.val * J + u.val) / J = b.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hu, zero_add]
    have hmod : (b.val * J + u.val) % J = u.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    ext <;> simp [hdiv, hmod]
  right_inv := fun k => by
    ext
    dsimp only
    rw [Nat.mul_comm, Nat.div_add_mod]

/-- Forward Stage 1 equivalence (`twoLayerFwdSt1` = `paramDFTStage1`). -/
lemma boolToZMod2_twoLayerFwdSt1 {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ZMod 2)
    (j2 : Fin (paramL2 n)) (q1 : Fin (paramL1 n)) (p : Fin (2 * paramJ n)) :
    let aB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (a ⟨idx, h⟩) else false
    boolToZMod2 (twoLayerFwdSt1 n aB j2.val q1.val p.val) =
      paramDFTStage1 n (paramSliceBlocks n a) j2 q1 p := by
  intro aB
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL2 : 0 < paramL2 n := one_le_paramL2 n
  have hL_eq : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hwExp : paramOmegaExp n = 3 * paramJ n / paramL n := paramOmegaExp_eq_div hn
  unfold twoLayerFwdSt1
  dsimp only
  rw [boolToZMod2_linearMapTarget]
  have hout_div : (q1.val * (2 * paramJ n) + p.val) / (2 * paramJ n) = q1.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2J, Nat.div_eq_of_lt p.isLt, zero_add]
  have hout_mod : (q1.val * (2 * paramJ n) + p.val) % (2 * paramJ n) = p.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]
  set inList := fwdSt1InIndices n (paramJ n) (paramL2 n) j2.val
  let itemFn : ℕ → ZMod 2 := fun idx =>
    monomialModVec (paramJ n) (paramOmegaExp n * (idx / paramJ n) * q1.val + idx % paramJ n) p *
      boolToZMod2 (aB idx)
  have hlhs_getD :
      Finset.univ.sum (fun k : Fin inList.length =>
        boolToZMod2 (fwdSt1Mat (paramJ n) (paramL1 n) (paramOmegaExp n) inList
          (q1.val * (2 * paramJ n) + p.val) k.val) *
          boolToZMod2 (aB (inList.getD k.val 0))) =
      (inList.map itemFn).sum := by
    refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
      (fin_length_getD_sum_eq_list_map_sum inList itemFn)
    unfold fwdSt1Mat
    dsimp only [itemFn]
    rw [hout_div, hout_mod]
    simp only [q1.isLt, decide_true, Bool.true_and]
    rw [boolToZMod2_coeffPowY hJ]
  rw [hlhs_getD]
  dsimp only [inList, fwdSt1InIndices, itemFn]
  rw [map_filter_sum_zmod2, list_range_map_sum_eq_fin_sum]
  unfold paramDFTStage1
  rw [vecDFTStage1_eq_flat_sum hJ hL_eq]
  unfold vecMulOmegaPow vecMulYExp paramSliceBlocks sliceBlocks
  dsimp only
  have hrhs_trim :
      Finset.univ.sum (fun j1 : Fin (paramL1 n) =>
        Finset.univ.sum (fun t : Fin (2 * paramJ n) =>
          (if _ : t.val < paramJ n then
            if hidx : paramJ n * (paramL2 n * j1.val + j2.val) + t.val < n then
              a ⟨paramJ n * (paramL2 n * j1.val + j2.val) + t.val, hidx⟩
            else 0
          else 0) *
            monomialModVec (paramJ n)
              (t.val + 3 * paramJ n / paramL n *
                (j2.val * q1.val + paramL2 n * (j1.val * q1.val))) p)) =
      Finset.univ.sum (fun j1 : Fin (paramL1 n) =>
        Finset.univ.sum (fun u : Fin (paramJ n) =>
          if hidx : paramJ n * (paramL2 n * j1.val + j2.val) + u.val < n then
            a ⟨paramJ n * (paramL2 n * j1.val + j2.val) + u.val, hidx⟩ *
              monomialModVec (paramJ n)
                (paramOmegaExp n * (paramL2 n * j1.val + j2.val) * q1.val + u.val) p
          else 0)) := by
    refine Finset.sum_congr rfl (fun j1 _ => ?_)
    rw [← Equiv.sum_comp (twoMulEquiv (paramJ n) hJ), Fintype.sum_prod_type]
    rw [Fin.sum_univ_two]
    have hzero_top :
        Finset.univ.sum (fun u : Fin (paramJ n) =>
          (if _ : (twoMulEquiv (paramJ n) hJ (1, u)).val < paramJ n then
            if hidx : paramJ n * (paramL2 n * j1.val + j2.val) +
                (twoMulEquiv (paramJ n) hJ (1, u)).val < n then
              a ⟨paramJ n * (paramL2 n * j1.val + j2.val) +
                (twoMulEquiv (paramJ n) hJ (1, u)).val, hidx⟩
            else 0
          else 0) *
            monomialModVec (paramJ n)
              ((twoMulEquiv (paramJ n) hJ (1, u)).val +
                3 * paramJ n / paramL n *
                  (j2.val * q1.val + paramL2 n * (j1.val * q1.val))) p) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      have hval : (twoMulEquiv (paramJ n) hJ (1, u)).val = paramJ n + u.val := by
        dsimp [twoMulEquiv]; omega
      have hnot : ¬ ((twoMulEquiv (paramJ n) hJ (1, u)).val < paramJ n) := by omega
      simp only [hnot, ↓reduceDIte, zero_mul]
    rw [hzero_top, add_zero]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have hval0 : (twoMulEquiv (paramJ n) hJ (0, u)).val = u.val := by
      dsimp [twoMulEquiv]; omega
    simp only [hval0, u.isLt, ↓reduceDIte]
    have hexp : u.val + 3 * paramJ n / paramL n *
        (j2.val * q1.val + paramL2 n * (j1.val * q1.val)) =
        paramOmegaExp n * (paramL2 n * j1.val + j2.val) * q1.val + u.val := by
      rw [hwExp]
      ring
    rw [hexp]
    split_ifs <;> ring
  rw [hrhs_trim]
  have hn_bound : n ≤ paramJ n * (paramL2 n * paramL1 n) := by
    calc
      n ≤ paramM n * paramJ n := le_paramM_mul_paramJ n
      _ ≤ paramL n * paramJ n := Nat.mul_le_mul_right (paramJ n) (paramM_le_paramL hn)
      _ = paramJ n * (paramL2 n * paramL1 n) := by rw [hL_eq]; ring
  have hrhs_prod := (Fintype.sum_prod_type (fun pair : Fin (paramL1 n) × Fin (paramJ n) =>
    if hidx : paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val < n then
      a ⟨paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val, hidx⟩ *
        monomialModVec (paramJ n)
          (paramOmegaExp n * (paramL2 n * pair.1.val + j2.val) * q1.val + pair.2.val) p
    else 0)).symm
  rw [hrhs_prod]
  have hlhs_each : ∀ idx : Fin n,
      boolToZMod2 (decide ((idx.val / paramJ n) % paramL2 n = j2.val)) *
        (monomialModVec (paramJ n)
          (paramOmegaExp n * (idx.val / paramJ n) * q1.val + idx.val % paramJ n) p *
          boolToZMod2 (aB idx.val)) =
      Finset.univ.sum (fun pair : Fin (paramL1 n) × Fin (paramJ n) =>
        if paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val = idx.val then
          a idx * monomialModVec (paramJ n)
            (paramOmegaExp n * (paramL2 n * pair.1.val + j2.val) * q1.val + pair.2.val) p
        else 0) := fun idx => by
    have haB : boolToZMod2 (aB idx.val) = a idx := by
      simp [aB]
    rw [haB]
    by_cases hmod : (idx.val / paramJ n) % paramL2 n = j2.val
    · simp only [hmod, decide_true, boolToZMod2_true, one_mul]
      have hr_lt : idx.val / paramJ n < paramL2 n * paramL1 n :=
        Nat.div_lt_of_lt_mul (lt_of_lt_of_le idx.isLt hn_bound)
      set p0 : Fin (paramL1 n) × Fin (paramJ n) :=
        (⟨(idx.val / paramJ n) / paramL2 n, Nat.div_lt_of_lt_mul hr_lt⟩,
         ⟨idx.val % paramJ n, Nat.mod_lt _ hJ⟩)
      have hp0_eq : paramJ n * (paramL2 n * p0.1.val + j2.val) + p0.2.val = idx.val := by
        dsimp [p0]
        have h1 : paramL2 n * ((idx.val / paramJ n) / paramL2 n) + j2.val =
            idx.val / paramJ n := by
          rw [← hmod]
          exact Nat.div_add_mod (idx.val / paramJ n) (paramL2 n)
        rw [h1]
        exact Nat.div_add_mod idx.val (paramJ n)
      have hsum :
          Finset.univ.sum (fun pair : Fin (paramL1 n) × Fin (paramJ n) =>
            if paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val = idx.val then
              a idx * monomialModVec (paramJ n)
                (paramOmegaExp n * (paramL2 n * pair.1.val + j2.val) * q1.val + pair.2.val) p
            else 0) =
          Finset.univ.sum (fun pair : Fin (paramL1 n) × Fin (paramJ n) =>
            if pair = p0 then
              a idx * monomialModVec (paramJ n)
                (paramOmegaExp n * (paramL2 n * p0.1.val + j2.val) * q1.val + p0.2.val) p
            else 0) := by
        refine Finset.sum_congr rfl (fun pair _ => ?_)
        by_cases hp : pair = p0
        · subst hp; simp [hp0_eq]
        · have hne : paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val ≠ idx.val := by
            intro heq
            apply hp
            have hdivJ : (paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val) /
                paramJ n = paramL2 n * pair.1.val + j2.val := by
              rw [Nat.mul_comm (paramJ n) _, Nat.add_comm, Nat.add_mul_div_right _ _ hJ,
                Nat.div_eq_of_lt pair.2.isLt, zero_add]
            have hmodJ : (paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val) %
                paramJ n = pair.2.val := by
              rw [Nat.mul_comm (paramJ n) _, Nat.add_comm, Nat.add_mul_mod_self_right,
                Nat.mod_eq_of_lt pair.2.isLt]
            have hr_eq : paramL2 n * pair.1.val + j2.val = idx.val / paramJ n := by
              rw [← heq, hdivJ]
            have hj1_eq : pair.1.val = (idx.val / paramJ n) / paramL2 n := by
              rw [← hr_eq, Nat.mul_comm (paramL2 n) _, Nat.add_comm,
                Nat.add_mul_div_right _ _ hL2, Nat.div_eq_of_lt j2.isLt, zero_add]
            have hu_eq : pair.2.val = idx.val % paramJ n := by rw [← heq, hmodJ]
            ext
            · exact hj1_eq
            · exact hu_eq
          simp [hp, hne]
      rw [hsum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hr0 : paramL2 n * p0.1.val + j2.val = idx.val / paramJ n := by
        dsimp [p0]
        rw [← hmod]
        exact Nat.div_add_mod (idx.val / paramJ n) (paramL2 n)
      have hu0 : p0.2.val = idx.val % paramJ n := rfl
      rw [hr0, hu0, mul_comm]
    · simp only [hmod, decide_false, boolToZMod2_false, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro pair _
      have hne : paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val ≠ idx.val := by
        intro heq
        have hdivJ : idx.val / paramJ n = paramL2 n * pair.1.val + j2.val := by
          rw [← heq, Nat.mul_comm (paramJ n) _, Nat.add_comm, Nat.add_mul_div_right _ _ hJ,
            Nat.div_eq_of_lt pair.2.isLt, zero_add]
        have hmodL2 : (idx.val / paramJ n) % paramL2 n = j2.val := by
          rw [hdivJ, Nat.mul_comm (paramL2 n) _, Nat.add_comm, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt j2.isLt]
        exact hmod hmodL2
      simp [hne]
  simp_rw [hlhs_each]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun pair _ => ?_)
  set m_idx := paramJ n * (paramL2 n * pair.1.val + j2.val) + pair.2.val
  by_cases hlt : m_idx < n
  · simp only [hlt, ↓reduceDIte]
    set idx0 : Fin n := ⟨m_idx, hlt⟩
    have hsum :
        Finset.univ.sum (fun idx : Fin n =>
          if m_idx = idx.val then
            a idx * monomialModVec (paramJ n)
              (paramOmegaExp n * (paramL2 n * pair.1.val + j2.val) * q1.val + pair.2.val) p
          else 0) =
        Finset.univ.sum (fun idx : Fin n =>
          if idx = idx0 then
            a idx0 * monomialModVec (paramJ n)
              (paramOmegaExp n * (paramL2 n * pair.1.val + j2.val) * q1.val + pair.2.val) p
          else 0) := by
      refine Finset.sum_congr rfl (fun idx _ => ?_)
      by_cases hi : idx = idx0
      · subst hi; simp [idx0]
      · have hne : m_idx ≠ idx.val := fun hv => hi (Fin.ext hv.symm)
        simp [hi, hne]
    rw [hsum]
    simp [idx0]
  · simp only [hlt, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro idx _
    have hne : m_idx ≠ idx.val := by omega
    simp [hne]

/-- Forward Stage 2 equivalence (`twoLayerFwdSt2` = `paramDFTStage2`). -/
lemma boolToZMod2_twoLayerFwdSt2 {n : ℕ} (hn : 1 ≤ n)
    (yB : ℕ → ℕ → ℕ → Bool)
    (yV : Fin (paramL2 n) → Fin (paramL1 n) → CoeffVec (paramJ n))
    (hy : ∀ (j2 : Fin (paramL2 n)) (q1 : Fin (paramL1 n)) (t : Fin (2 * paramJ n)),
      boolToZMod2 (yB j2.val q1.val t.val) = yV j2 q1 t)
    (q : Fin (paramL n)) (p : Fin (2 * paramJ n)) :
    boolToZMod2 (twoLayerFwdSt2 n yB q.val p.val) = paramDFTStage2 n yV q p := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL_eq : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hwExp : paramOmegaExp n = 3 * paramJ n / paramL n := paramOmegaExp_eq_div hn
  have hq2_lt : q.val / paramL1 n < paramL2 n :=
    Nat.div_lt_of_lt_mul (by rw [← hL_eq]; exact q.isLt)
  unfold twoLayerFwdSt2
  dsimp only
  rw [boolToZMod2_linearMapTarget]
  rw [← Equiv.sum_comp (blockSplitEquiv (2 * paramJ n) (paramL2 n) h2J), Fintype.sum_prod_type]
  unfold paramDFTStage2 vecDFTStage2Flat vecDFTStage2 vecMulOmegaPow vecMulYExp
  have hout_div : ((q.val / paramL1 n) * (2 * paramJ n) + p.val) / (2 * paramJ n) =
      q.val / paramL1 n := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2J, Nat.div_eq_of_lt p.isLt, zero_add]
  have hout_mod : ((q.val / paramL1 n) * (2 * paramJ n) + p.val) % (2 * paramJ n) = p.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold st2Mat
  dsimp only
  rw [hout_div, hout_mod, blockSplitEquiv_div, blockSplitEquiv_mod]
  simp only [hq2_lt, j2.isLt, and_self, decide_true, Bool.true_and]
  rw [boolToZMod2_coeffPowY hJ, hy j2 ⟨q.val % paramL1 n, Nat.mod_lt _ hL1⟩ t]
  have hexp : paramOmegaExp n * paramL1 n * j2.val * (q.val / paramL1 n) + t.val =
      t.val + 3 * paramJ n / paramL n * (paramL1 n * (j2.val * (q.val / paramL1 n))) := by
    rw [hwExp]
    ring
  rw [hexp, mul_comm]

/-- Pointwise ring multiplication equivalence (`ringMulBits` = `vecMul`). -/
lemma boolToZMod2_ringMulBits {J : ℕ} (hJ : 0 < J)
    (uB vB : ℕ → Bool) (uV vV : CoeffVec J)
    (hu : ∀ t : Fin (2 * J), boolToZMod2 (uB t.val) = uV t)
    (hv : ∀ t : Fin (2 * J), boolToZMod2 (vB t.val) = vV t)
    (p : Fin (2 * J)) :
    boolToZMod2 (ringMulBits J uB vB p.val) = vecMul J uV vV p := by
  have h2J : 0 < 2 * J := by omega
  unfold ringMulBits
  rw [boolToZMod2_bilinearMapTarget (2 * J) (2 * J) h2J]
  unfold vecMul ringMulTensor
  refine Finset.sum_congr rfl (fun t1 _ => ?_)
  refine Finset.sum_congr rfl (fun t2 _ => ?_)
  have ht1 : t1.val < 2 * J := t1.isLt
  have ht2_not : ¬ (2 * J + t2.val < 2 * J) := by omega
  have ht2_sub : 2 * J + t2.val - 2 * J = t2.val := by omega
  simp only [ht1, ht2_not, ↓reduceIte, ht2_sub]
  rw [boolToZMod2_coeffPowY hJ, hu t1, hv t2, mul_comm]

/-- Inverse Stage 1 equivalence (`twoLayerInvSt1` = `paramIDFTStage1`). -/
lemma boolToZMod2_twoLayerInvSt1 {n : ℕ} (hn : 1 ≤ n)
    (fcB : ℕ → ℕ → Bool)
    (fcV : Fin (paramL n) → CoeffVec (paramJ n))
    (hfc : ∀ (r : Fin (paramL n)) (t : Fin (2 * paramJ n)),
      boolToZMod2 (fcB r.val t.val) = fcV r t)
    (j2 : Fin (paramL2 n)) (q1 : Fin (paramL1 n)) (p : Fin (2 * paramJ n)) :
    boolToZMod2 (twoLayerInvSt1 n fcB j2.val q1.val p.val) =
      paramIDFTStage1 n fcV j2 q1 p := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL_eq : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hinvExp : paramInvOmegaExp n = (3 * paramJ n / paramL n) * (paramL n - 1) :=
    paramInvOmegaExp_eq hn
  unfold twoLayerInvSt1
  dsimp only
  rw [boolToZMod2_linearMapTarget]
  rw [← Equiv.sum_comp (blockSplitEquiv (2 * paramJ n) (paramL1 n) h2J), Fintype.sum_prod_type]
  unfold paramIDFTStage1
  rw [vecIDFTStage1_eq_flat_sum hJ hL_eq]
  unfold vecMulOmegaInvPow vecMulOmegaPow vecMulYExp
  have hout_div : (q1.val * (2 * paramJ n) + p.val) / (2 * paramJ n) = q1.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2J, Nat.div_eq_of_lt p.isLt, zero_add]
  have hout_mod : (q1.val * (2 * paramJ n) + p.val) % (2 * paramJ n) = p.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold fullSt1Mat
  dsimp only
  rw [hout_div, hout_mod, blockSplitEquiv_div, blockSplitEquiv_mod]
  simp only [q1.isLt, j1.isLt, and_self, decide_true, Bool.true_and]
  rw [boolToZMod2_coeffPowY hJ, hfc ⟨paramL2 n * j1.val + j2.val, stage1_idx_lt hL_eq j1 j2⟩ t]
  have hexp : paramInvOmegaExp n * (paramL2 n * j1.val + j2.val) * q1.val + t.val =
      t.val + 3 * paramJ n / paramL n *
        ((paramL n - 1) * (j2.val * q1.val + paramL2 n * (j1.val * q1.val))) := by
    rw [hinvExp]
    ring
  rw [hexp, mul_comm]

/-- Inverse Stage 2 equivalence (`twoLayerInvSt2` = `paramIDFTStage2`). -/
lemma boolToZMod2_twoLayerInvSt2 {n : ℕ} (hn : 1 ≤ n)
    (ycB : ℕ → ℕ → ℕ → Bool)
    (ycV : Fin (paramL2 n) → Fin (paramL1 n) → CoeffVec (paramJ n))
    (hyc : ∀ (j2 : Fin (paramL2 n)) (q1 : Fin (paramL1 n)) (t : Fin (2 * paramJ n)),
      boolToZMod2 (ycB j2.val q1.val t.val) = ycV j2 q1 t)
    (r : Fin (paramL n)) (p : Fin (2 * paramJ n)) :
    boolToZMod2 (twoLayerInvSt2 n ycB r.val p.val) = paramIDFTStage2 n ycV r p := by
  have hJ : 0 < paramJ n := paramJ_pos n
  have h2J : 0 < 2 * paramJ n := by omega
  have hL1 : 0 < paramL1 n := one_le_paramL1 n
  have hL_eq : paramL n = paramL1 n * paramL2 n := paramL_eq_mul n
  have hinvExp : paramInvOmegaExp n = (3 * paramJ n / paramL n) * (paramL n - 1) :=
    paramInvOmegaExp_eq hn
  have hq2_lt : r.val / paramL1 n < paramL2 n :=
    Nat.div_lt_of_lt_mul (by rw [← hL_eq]; exact r.isLt)
  unfold twoLayerInvSt2
  dsimp only
  rw [boolToZMod2_linearMapTarget]
  rw [← Equiv.sum_comp (blockSplitEquiv (2 * paramJ n) (paramL2 n) h2J), Fintype.sum_prod_type]
  unfold paramIDFTStage2 vecIDFTStage2Flat vecIDFTStage2 vecMulOmegaInvPow
    vecMulOmegaPow vecMulYExp
  have hout_div : ((r.val / paramL1 n) * (2 * paramJ n) + p.val) / (2 * paramJ n) =
      r.val / paramL1 n := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2J, Nat.div_eq_of_lt p.isLt, zero_add]
  have hout_mod : ((r.val / paramL1 n) * (2 * paramJ n) + p.val) % (2 * paramJ n) = p.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt]
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold st2Mat
  dsimp only
  rw [hout_div, hout_mod, blockSplitEquiv_div, blockSplitEquiv_mod]
  simp only [hq2_lt, j2.isLt, and_self, decide_true, Bool.true_and]
  rw [boolToZMod2_coeffPowY hJ, hyc j2 ⟨r.val % paramL1 n, Nat.mod_lt _ hL1⟩ t]
  have hexp : paramInvOmegaExp n * paramL1 n * j2.val * (r.val / paramL1 n) + t.val =
      t.val + 3 * paramJ n / paramL n *
        ((paramL n - 1) * (paramL1 n * (j2.val * (r.val / paramL1 n)))) := by
    rw [hinvExp]
    ring
  rw [hexp, mul_comm]

/-- Full `2n`-bit polynomial product bit equivalence (`twoLayerPolyMulBit` = `polyFullConv`). -/
lemma boolToZMod2_twoLayerPolyMulBit {n : ℕ} (hn : 1 ≤ n) (a b : Fin n → ZMod 2)
    (k : Fin (2 * n)) :
    let aB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (a ⟨idx, h⟩) else false
    let bB : ℕ → Bool := fun idx => if h : idx < n then zmod2ToBool (b ⟨idx, h⟩) else false
    boolToZMod2 (twoLayerPolyMulBit n aB bB k.val) = polyFullConv n a b k := by
  intro aB bB
  have hJ : 0 < paramJ n := paramJ_pos n
  let yaB := twoLayerFwdSt1 n aB
  let faB := twoLayerFwdSt2 n yaB
  let ybB := twoLayerFwdSt1 n bB
  let fbB := twoLayerFwdSt2 n ybB
  let fcB := fun q p => ringMulBits (paramJ n) (faB q) (fbB q) p
  let ycB := twoLayerInvSt1 n fcB
  let crawB := twoLayerInvSt2 n ycB
  let yaV := paramDFTStage1 n (paramSliceBlocks n a)
  let faV := paramDFTStage2 n yaV
  let ybV := paramDFTStage1 n (paramSliceBlocks n b)
  let fbV := paramDFTStage2 n ybV
  let fcV := paramPointwiseMul n faV fbV
  let ycV := paramIDFTStage1 n fcV
  let crawV := paramIDFTStage2 n ycV
  have hya : ∀ j2 q1 t, boolToZMod2 (yaB j2.val q1.val t.val) = yaV j2 q1 t :=
    fun j2 q1 t => boolToZMod2_twoLayerFwdSt1 hn a j2 q1 t
  have hfa : ∀ q t, boolToZMod2 (faB q.val t.val) = faV q t :=
    fun q t => boolToZMod2_twoLayerFwdSt2 hn yaB yaV hya q t
  have hyb : ∀ j2 q1 t, boolToZMod2 (ybB j2.val q1.val t.val) = ybV j2 q1 t :=
    fun j2 q1 t => boolToZMod2_twoLayerFwdSt1 hn b j2 q1 t
  have hfb : ∀ q t, boolToZMod2 (fbB q.val t.val) = fbV q t :=
    fun q t => boolToZMod2_twoLayerFwdSt2 hn ybB ybV hyb q t
  have hfc : ∀ q t, boolToZMod2 (fcB q.val t.val) = fcV q t :=
    fun q t => boolToZMod2_ringMulBits hJ (faB q.val) (fbB q.val) (faV q) (fbV q)
      (hfa q) (hfb q) t
  have hyc : ∀ j2 q1 t, boolToZMod2 (ycB j2.val q1.val t.val) = ycV j2 q1 t :=
    fun j2 q1 t => boolToZMod2_twoLayerInvSt1 hn fcB fcV hfc j2 q1 t
  have hcraw : ∀ r t, boolToZMod2 (crawB r.val t.val) = crawV r t :=
    fun r t => boolToZMod2_twoLayerInvSt2 hn ycB ycV hyc r t
  change boolToZMod2 (bne
    (if k.val / paramJ n < paramL n then crawB (k.val / paramJ n) (k.val % paramJ n) else false)
    (if 0 < k.val / paramJ n ∧ k.val / paramJ n - 1 < paramL n then
      crawB (k.val / paramJ n - 1) (paramJ n + k.val % paramJ n) else false)) =
    polyFullConv n a b k
  rw [boolToZMod2_bne]
  rw [← paramReconstructFull_paramConvBlocks_eq_polyFullConv hn a b]
  change _ = paramReconstructFull n crawV k
  unfold paramReconstructFull reconstructFull overlapBlock blockLo blockHi
  have hu_lt : k.val % paramJ n < paramJ n := Nat.mod_lt k.val hJ
  have hu2_lt : k.val % paramJ n < 2 * paramJ n := by omega
  have hJu_lt : paramJ n + k.val % paramJ n < 2 * paramJ n := by omega
  congr 1
  · by_cases hr : k.val / paramJ n < paramL n
    · simp only [hr, ↓reduceIte, ↓reduceDIte]
      exact hcraw ⟨k.val / paramJ n, hr⟩ ⟨k.val % paramJ n, hu2_lt⟩
    · simp only [hr, ↓reduceIte, ↓reduceDIte, boolToZMod2_false]
  · by_cases hr0 : k.val / paramJ n = 0
    · have hnot : ¬ (0 < k.val / paramJ n ∧ k.val / paramJ n - 1 < paramL n) := by omega
      simp only [hnot, ↓reduceIte, boolToZMod2_false]
      simp only [hr0, ↓reduceIte]
    · have hrpos : 0 < k.val / paramJ n := Nat.pos_of_ne_zero hr0
      simp only [hr0, ↓reduceIte]
      by_cases hr1 : k.val / paramJ n - 1 < paramL n
      · simp only [hrpos, hr1, and_self, ↓reduceIte, ↓reduceDIte]
        exact hcraw ⟨k.val / paramJ n - 1, hr1⟩ ⟨paramJ n + k.val % paramJ n, hJu_lt⟩
      · simp only [hrpos, hr1, and_false, ↓reduceIte, ↓reduceDIte, boolToZMod2_false]

/-- **Main Glue Theorem**: Branch 3's concrete 2-layer Boolean polynomial multiplication + cyclic
folding equals `QCSD_cycMul` for all `n ≥ 1`. -/
theorem twoLayerConvSpec_holds {n : ℕ} (hn : 1 ≤ n) : TwoLayerConvSpec n := by
  intro a b i
  unfold twoLayerCycMul
  dsimp only
  rw [boolToZMod2_bne]
  have h1 := boolToZMod2_twoLayerPolyMulBit hn a b ⟨i.val, by omega⟩
  have h2 := boolToZMod2_twoLayerPolyMulBit hn a b ⟨i.val + n, by omega⟩
  dsimp only at h1 h2
  rw [h1, h2]
  exact (QCSD_cycMul_eq_polyFullConv_fold n a b i).symm

end GlueTwoLayerConv
