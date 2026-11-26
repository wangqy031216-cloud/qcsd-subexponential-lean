import Branch6_EncoderMacros

namespace Branch6Encoder

open QCSD.Defs
open Branch5PadAndSep

/-!
## Section 3a: Concrete Register Layout (`EncR`), Input Parsers, and Parameter Computation

Zero custom `structure`, `inductive`, or `class` declarations.
All parameter and network offset definitions are definitionally identical to `Branch3_Network.lean`.
-/

/-- Fixed 56-register bank shared across input parsing, parameter computation, and edge emission.
Liftable to any larger register bank via `rmLift`. -/
abbrev EncR : ℕ := 56

abbrev regN         : Fin EncR := 0
abbrev regK         : Fin EncR := 1
abbrev regJ         : Fin EncR := ⟨2, by decide⟩
abbrev regM         : Fin EncR := ⟨3, by decide⟩
abbrev regEll       : Fin EncR := ⟨4, by decide⟩
abbrev regL         : Fin EncR := ⟨5, by decide⟩
abbrev regL1        : Fin EncR := ⟨6, by decide⟩
abbrev regL2        : Fin EncR := ⟨7, by decide⟩
abbrev regOmega     : Fin EncR := ⟨8, by decide⟩
abbrev regInvOmega  : Fin EncR := ⟨9, by decide⟩
abbrev regTreeLog   : Fin EncR := ⟨10, by decide⟩
abbrev regTreeM     : Fin EncR := ⟨11, by decide⟩
abbrev regVertCount : Fin EncR := ⟨12, by decide⟩
abbrev regEdgeCount : Fin EncR := ⟨13, by decide⟩
abbrev regV1        : Fin EncR := ⟨14, by decide⟩
abbrev regV2        : Fin EncR := ⟨15, by decide⟩
abbrev regV3        : Fin EncR := ⟨16, by decide⟩
abbrev regV4        : Fin EncR := ⟨17, by decide⟩
abbrev regV5        : Fin EncR := ⟨18, by decide⟩
abbrev regV6        : Fin EncR := ⟨19, by decide⟩
abbrev regV7        : Fin EncR := ⟨20, by decide⟩
abbrev regV8        : Fin EncR := ⟨21, by decide⟩
abbrev regV9        : Fin EncR := ⟨22, by decide⟩
abbrev regV10       : Fin EncR := ⟨23, by decide⟩
abbrev regV11       : Fin EncR := ⟨24, by decide⟩
abbrev regV12       : Fin EncR := ⟨25, by decide⟩
abbrev regV13       : Fin EncR := ⟨26, by decide⟩
abbrev regV14       : Fin EncR := ⟨27, by decide⟩
abbrev regV15       : Fin EncR := ⟨28, by decide⟩
abbrev regV16       : Fin EncR := ⟨29, by decide⟩
abbrev regV17       : Fin EncR := ⟨30, by decide⟩
abbrev regV18       : Fin EncR := ⟨31, by decide⟩
abbrev regTwoJ      : Fin EncR := ⟨32, by decide⟩
abbrev regTwoJL     : Fin EncR := ⟨33, by decide⟩
abbrev regCur       : Fin EncR := ⟨34, by decide⟩
abbrev regOffH      : Fin EncR := ⟨35, by decide⟩
abbrev regOffS      : Fin EncR := ⟨36, by decide⟩
abbrev regT0        : Fin EncR := ⟨37, by decide⟩
abbrev regT1        : Fin EncR := ⟨38, by decide⟩
abbrev regPreLen    : Fin EncR := ⟨39, by decide⟩
abbrev regOffPre    : Fin EncR := ⟨40, by decide⟩
abbrev regS0        : Fin EncR := ⟨41, by decide⟩
abbrev regS1        : Fin EncR := ⟨42, by decide⟩
abbrev regS2        : Fin EncR := ⟨43, by decide⟩
abbrev regS3        : Fin EncR := ⟨44, by decide⟩
abbrev regS4        : Fin EncR := ⟨45, by decide⟩
abbrev regS5        : Fin EncR := ⟨46, by decide⟩
abbrev regS6        : Fin EncR := ⟨47, by decide⟩
abbrev regS7        : Fin EncR := ⟨48, by decide⟩
abbrev regLoopI     : Fin EncR := ⟨49, by decide⟩
abbrev regLoopRem   : Fin EncR := ⟨50, by decide⟩
abbrev regLoopJ     : Fin EncR := ⟨51, by decide⟩
abbrev regLoopNode  : Fin EncR := ⟨52, by decide⟩
abbrev regLoopW     : Fin EncR := ⟨53, by decide⟩
abbrev regEndU      : Fin EncR := ⟨54, by decide⟩
abbrev regEndV      : Fin EncR := ⟨55, by decide⟩

@[simp] lemma regUpd_fin_ne {R : ℕ} (reg : RegState R) (a b : Fin R)
    (v : ℕ) (h : b.val ≠ a.val) :
    regUpd reg a v b = reg b :=
  regUpd_ne reg (fun heq => h (congrArg Fin.val heq)) v

/-! ### Unary Input Scanner (`rmReadUnary`) and Input Parsers (`rmParseInputStd`, `rmParseInputSep`) -/

abbrev RMReadUnaryQ : Type := Bool ⊕ ((Option Bool ⊕ (Unit ⊕ (Bool ⊕ Bool))) ⊕ Bool)

/-- Scans `QCSD_natToUnary m` starting at `reg rCur`, storing `m` in `rVal` and advancing
`rCur` past the terminating `false` bit (`rCur := rCur + m + 1`). -/
def rmReadUnary {R : ℕ} (rCur rVal : Fin R) : RMProg R RMReadUnaryQ :=
  rmChain (rmZero rVal)
    (rmChain (rmWhileReadIn rCur (rmChain (rmInc rCur) (rmInc rVal) false) (Sum.inl false))
      (rmInc rCur) false)
    (Sum.inl rmWhileReadInEntry)

def rmReadUnaryEntry : RMReadUnaryQ := Sum.inl false
def rmReadUnaryExit : RMReadUnaryQ := Sum.inr (Sum.inr true)

lemma rmReadUnary_loop_spec {R : ℕ} (rCur rVal : Fin R) (hcv : rCur ≠ rVal)
    (V : ℕ) (inp : List Bool) :
    ∀ (rem : ℕ) (reg : RegState R),
      (∀ j < rem, inp.getD (reg rCur + j) false = true) →
      inp.getD (reg rCur + rem) false = false →
      (∀ i, reg i ≤ V) →
      reg rCur + rem ≤ V →
      reg rVal + rem ≤ V →
      RMExec (rmWhileReadIn rCur (rmChain (rmInc rCur) (rmInc rVal) false) (Sum.inl false))
        V inp rmWhileReadInEntry reg rmWhileReadInExit
        (regUpd (regUpd reg rCur (reg rCur + rem)) rVal (reg rVal + rem)) [] (3 * rem + 1)
  | 0, reg, _, hstop, hreg, _, _ => by
    have hupd : regUpd (regUpd reg rCur (reg rCur + 0)) rVal (reg rVal + 0) = reg := by
      simp
    rw [hupd]
    simpa using rmWhileReadIn_false rCur _ _ V inp reg (by simpa using hstop) hreg
  | rem + 1, reg, htrues, hstop, hreg, hcurV, hvalV => by
    have hb : inp.getD (reg rCur) false = true := by simpa using htrues 0 (by omega)
    have hi1 := rmInc_spec rCur V inp reg hreg (by omega)
    set reg1 := regUpd reg rCur (reg rCur + 1)
    have h1_val : reg1 rVal = reg rVal := regUpd_ne reg hcv.symm _
    have hi2 := rmInc_spec rVal V inp reg1 hi1.reg₁_le (by rw [h1_val]; omega)
    set reg2 := regUpd reg1 rVal (reg1 rVal + 1)
    have h2_cur : reg2 rCur = reg rCur + 1 := by
      dsimp only [reg2, reg1]; rw [regUpd_ne _ hcv, regUpd_self]
    have h2_val : reg2 rVal = reg rVal + 1 := by dsimp only [reg2]; rw [regUpd_self, h1_val]
    have hbody := rmChain_spec_inl (by simp [rmInc]) hi1 hi2
    simp only [max_self, List.nil_append] at hbody
    have hrest := rmReadUnary_loop_spec rCur rVal hcv V inp rem reg2
      (fun j hj => by rw [h2_cur]; convert htrues (j + 1) (by omega) using 2; omega)
      (by rw [h2_cur]; convert hstop using 2; omega)
      hi2.reg₁_le (by rw [h2_cur]; omega) (by rw [h2_val]; omega)
    have hupd : regUpd (regUpd reg2 rCur (reg2 rCur + rem)) rVal (reg2 rVal + rem) =
        regUpd (regUpd reg rCur (reg rCur + (rem + 1))) rVal (reg rVal + (rem + 1)) := by
      funext i
      by_cases hiv : i = rVal
      · subst hiv; simp [h2_val]; omega
      · by_cases hic : i = rCur
        · subst hic; simp [regUpd_ne _ hcv, h2_cur]; omega
        · simp [regUpd, hiv, hic, reg2, reg1]
    rw [hupd] at hrest
    have hstep := rmWhileReadIn_step rCur _ hb hbody hrest
    simpa [max_self, show 1 + (1 + 1) + (3 * rem + 1) = 3 * (rem + 1) + 1 by omega] using hstep

theorem rmReadUnary_spec {R : ℕ} (rCur rVal : Fin R) (hcv : rCur ≠ rVal)
    (m V : ℕ) (inp : List Bool) (reg : RegState R)
    (htrues : ∀ j < m, inp.getD (reg rCur + j) false = true)
    (hstop : inp.getD (reg rCur + m) false = false)
    (hreg : ∀ i, reg i ≤ V) (hcurV : reg rCur + m + 1 ≤ V) (hmV : m ≤ V) :
    RMExec (rmReadUnary rCur rVal) V inp rmReadUnaryEntry reg rmReadUnaryExit
      (regUpd (regUpd reg rCur (reg rCur + m + 1)) rVal m) [] (3 * m + 3) := by
  have hz := rmZero_spec rVal V inp reg hreg
  set reg1 := regUpd reg rVal 0
  have h1_cur : reg1 rCur = reg rCur := regUpd_ne reg hcv 0
  have h1_val : reg1 rVal = 0 := regUpd_self reg rVal 0
  have hloop := rmReadUnary_loop_spec rCur rVal hcv V inp m reg1
    (by simpa [h1_cur] using htrues) (by simpa [h1_cur] using hstop)
    hz.reg₁_le (by rw [h1_cur]; omega) (by rw [h1_val]; omega)
  set reg2 := regUpd (regUpd reg1 rCur (reg1 rCur + m)) rVal (reg1 rVal + m)
  have h2_cur : reg2 rCur = reg rCur + m := by
    dsimp only [reg2]; rw [regUpd_ne _ hcv, regUpd_self, h1_cur]
  have hi := rmInc_spec rCur V inp reg2 hloop.reg₁_le (by rw [h2_cur]; exact hcurV)
  have hupd : regUpd reg2 rCur (reg2 rCur + 1) =
      regUpd (regUpd reg rCur (reg rCur + m + 1)) rVal m := by
    funext i
    by_cases hiv : i = rVal
    · subst hiv; simp [regUpd_ne _ hcv.symm, reg2, h1_val]
    · by_cases hic : i = rCur
      · subst hic; simp [regUpd_ne _ hcv, h2_cur]
      · simp [regUpd, hiv, hic, reg2, reg1]
  rw [hupd] at hi
  have hact_loop : rmWhileReadIn rCur (rmChain (rmInc rCur) (rmInc rVal) false) (Sum.inl false)
      rmWhileReadInEntry ≠ none := by
    simp [rmWhileReadIn, rmWhileReadInEntry, rmLoop, rmIfReadIn, rmIfReadInEntry, rmSeq, rmReadInProg]
  have h23 := rmChain_spec_inl hact_loop hloop hi
  have h123 := rmChain_spec_inl (by simp [rmZero]) hz h23
  simpa [rmReadUnary, rmReadUnaryEntry, rmReadUnaryExit, max_self,
    show 1 + (3 * m + 1 + 1) = 3 * m + 3 by omega] using h123

/-! ### Encoding Index Lemmas for `QCSD_natToUnary` and `QCSD_vecToBits` -/

lemma natToUnary_length (m : ℕ) : (QCSD_natToUnary m).length = m + 1 := by
  simp [QCSD_natToUnary]

lemma vecToBits_length {n : ℕ} (v : Fin n → ZMod 2) : (QCSD_vecToBits v).length = n := by
  simp [QCSD_vecToBits]

lemma list_getD_append_left' (l₁ l₂ : List Bool) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma list_getD_append_right' (l₁ l₂ : List Bool) {i : ℕ} (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i false = l₂.getD (i - l₁.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma natToUnary_getD_lt (m : ℕ) {j : ℕ} (hj : j < m) :
    (QCSD_natToUnary m).getD j false = true := by
  unfold QCSD_natToUnary
  rw [list_getD_append_left' _ _ (by simp; exact hj)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma natToUnary_getD_eq (m : ℕ) :
    (QCSD_natToUnary m).getD m false = false := by
  unfold QCSD_natToUnary
  rw [list_getD_append_right' _ _ (by simp)]
  simp

lemma vecToBits_getD {n : ℕ} (v : Fin n → ZMod 2) {i : ℕ} (hi : i < n) :
    (QCSD_vecToBits v).getD i false = decide (v ⟨i, hi⟩ = (1 : ZMod 2)) := by
  unfold QCSD_vecToBits
  simp [List.getD_eq_getElem?_getD, hi]

lemma slice_getD_eq (pref mid suf : List Bool) {j : ℕ} (hj : j < mid.length) :
    (pref ++ mid ++ suf).getD (pref.length + j) false = mid.getD j false := by
  rw [List.append_assoc, list_getD_append_right' pref (mid ++ suf) (by omega)]
  have hsub : pref.length + j - pref.length = j := by omega
  rw [hsub, list_getD_append_left' mid suf hj]

/-! ### Input Parser for Standard (`Exact`/`Le`) Format and Separate (`Sep`) Format -/

/-- Shared prefix parser: reads `n`, records `offH = n + 1`, `offS = 2n + 1`, advances `cur = 3n + 1`. -/
abbrev RMParsePrefixQ : Type :=
  Bool ⊕ (RMReadUnaryQ ⊕ (Bool ⊕ (RMAddQ ⊕ (Bool ⊕ RMAddQ))))

def rmParsePrefix : RMProg EncR RMParsePrefixQ :=
  rmChain (rmZero regCur)
    (rmChain (rmReadUnary regCur regN)
      (rmChain (rmCopy regOffH regCur)
        (rmChain (rmAdd regCur regN regS0)
          (rmChain (rmCopy regOffS regCur)
            (rmAdd regCur regN regS0)
            rmAddEntry)
          (Sum.inl false))
        (Sum.inl rmAddEntry))
      (Sum.inl false))
    (Sum.inl rmReadUnaryEntry)

def rmParsePrefixEntry : RMParsePrefixQ := Sum.inl false
def rmParsePrefixExit : RMParsePrefixQ := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmAddExit))))

lemma rmParsePrefix_spec {n : ℕ} (h s : Fin n → ZMod 2) (rest : List Bool)
    (V : ℕ) (reg₀ : RegState EncR)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 3 * n + 1 ≤ V) :
    let inp := QCSD_natToUnary n ++ QCSD_vecToBits h ++ QCSD_vecToBits s ++ rest
    ∃ reg₁ : RegState EncR,
      reg₁ regN = n ∧
      reg₁ regOffH = n + 1 ∧
      reg₁ regOffS = 2 * n + 1 ∧
      reg₁ regCur = 3 * n + 1 ∧
      (∀ (i : ℕ) (hi : i < n), inp.getD (reg₁ regOffH + i) false = decide (h ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      (∀ (i : ℕ) (hi : i < n), inp.getD (reg₁ regOffS + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      RMExec rmParsePrefix V inp rmParsePrefixEntry reg₀ rmParsePrefixExit reg₁ [] (7 * n + 10) := by
  intro inp
  have hz := rmZero_spec regCur V inp reg₀ hreg₀
  set r1 := regUpd reg₀ regCur 0
  have h1_cur : r1 regCur = 0 := regUpd_self _ _ _
  have hinp_assoc : inp = QCSD_natToUnary n ++ (QCSD_vecToBits h ++ QCSD_vecToBits s ++ rest) := by
    simp [inp, List.append_assoc]
  have hru := rmReadUnary_spec regCur regN (by decide) n V inp r1
    (fun j hj => by
      rw [h1_cur, Nat.zero_add, hinp_assoc, list_getD_append_left' _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt n hj)
    (by
      rw [h1_cur, Nat.zero_add, hinp_assoc, list_getD_append_left' _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq n)
    hz.reg₁_le (by rw [h1_cur]; omega) (by omega)
  set r2 := regUpd (regUpd r1 regCur (r1 regCur + n + 1)) regN n
  have h2_cur : r2 regCur = n + 1 := by
    dsimp only [r2]; rw [regUpd_ne _ (by decide), regUpd_self, h1_cur, Nat.zero_add]
  have h2_n : r2 regN = n := regUpd_self _ _ _
  have hc1 := rmCopy_spec regOffH regCur V inp r2 hru.reg₁_le
  set r3 := regUpd r2 regOffH (r2 regCur)
  have h3_cur : r3 regCur = n + 1 := by dsimp only [r3]; rw [regUpd_ne _ (by decide), h2_cur]
  have h3_n : r3 regN = n := by dsimp only [r3]; rw [regUpd_ne _ (by decide), h2_n]
  have h3_oH : r3 regOffH = n + 1 := by dsimp only [r3]; rw [regUpd_self, h2_cur]
  have ha1 := rmAdd_spec regCur regN regS0 (by decide) (by decide) V inp r3 hc1.reg₁_le
    (by rw [h3_cur, h3_n]; omega)
  set r4 := regUpd (regUpd r3 regCur (r3 regCur + r3 regN)) regS0 0
  have h4_cur : r4 regCur = 2 * n + 1 := by
    dsimp only [r4]; rw [regUpd_ne _ (by decide), regUpd_self, h3_cur, h3_n]; omega
  have h4_n : r4 regN = n := by
    dsimp only [r4]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h3_n]
  have h4_oH : r4 regOffH = n + 1 := by
    dsimp only [r4]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h3_oH]
  have hc2 := rmCopy_spec regOffS regCur V inp r4 ha1.reg₁_le
  set r5 := regUpd r4 regOffS (r4 regCur)
  have h5_cur : r5 regCur = 2 * n + 1 := by dsimp only [r5]; rw [regUpd_ne _ (by decide), h4_cur]
  have h5_n : r5 regN = n := by dsimp only [r5]; rw [regUpd_ne _ (by decide), h4_n]
  have h5_oH : r5 regOffH = n + 1 := by dsimp only [r5]; rw [regUpd_ne _ (by decide), h4_oH]
  have h5_oS : r5 regOffS = 2 * n + 1 := by dsimp only [r5]; rw [regUpd_self, h4_cur]
  have ha2 := rmAdd_spec regCur regN regS0 (by decide) (by decide) V inp r5 hc2.reg₁_le
    (by rw [h5_cur, h5_n]; omega)
  set r6 := regUpd (regUpd r5 regCur (r5 regCur + r5 regN)) regS0 0
  have h6_cur : r6 regCur = 3 * n + 1 := by
    dsimp only [r6]; rw [regUpd_ne _ (by decide), regUpd_self, h5_cur, h5_n]; omega
  have h6_n : r6 regN = n := by
    dsimp only [r6]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h5_n]
  have h6_oH : r6 regOffH = n + 1 := by
    dsimp only [r6]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h5_oH]
  have h6_oS : r6 regOffS = 2 * n + 1 := by
    dsimp only [r6]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h5_oS]
  have h56 := rmChain_spec_inl (by simp [rmCopy]) hc2 ha2
  have h46 := rmChain_spec_inl (by simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]) ha1 h56
  have h36 := rmChain_spec_inl (by simp [rmCopy]) hc1 h46
  have h26 := rmChain_spec_inl (by simp [rmReadUnary, rmReadUnaryEntry, rmChain, rmSeq, rmZero]) hru h36
  have h16 := rmChain_spec_inl (by simp [rmZero]) hz h26
  have hT : 1 + (3 * n + 3 + (1 + (2 * r3 regN + 2 + (1 + (2 * r5 regN + 2))))) = 7 * n + 10 := by
    rw [h3_n, h5_n]; ring
  rw [max_self, max_self, max_self, max_self, max_self,
      List.nil_append, List.nil_append, List.nil_append, List.nil_append, List.nil_append, hT] at h16
  refine ⟨r6, h6_n, h6_oH, h6_oS, h6_cur, ?_, ?_, h16⟩
  · intro i hi
    rw [h6_oH]
    have h1 : (QCSD_natToUnary n).length = n + 1 := natToUnary_length n
    have hsplit : inp = QCSD_natToUnary n ++ QCSD_vecToBits h ++ (QCSD_vecToBits s ++ rest) := by
      simp [inp, List.append_assoc]
    rw [hsplit, ← h1, slice_getD_eq _ _ _ (by rw [vecToBits_length]; exact hi)]
    exact vecToBits_getD h hi
  · intro i hi
    rw [h6_oS]
    have h1 : (QCSD_natToUnary n ++ QCSD_vecToBits h).length = 2 * n + 1 := by
      rw [List.length_append, natToUnary_length, vecToBits_length]; omega
    rw [← h1]
    have hslice := slice_getD_eq (QCSD_natToUnary n ++ QCSD_vecToBits h) (QCSD_vecToBits s) rest
      (by rw [vecToBits_length]; exact hi)
    rw [hslice]
    exact vecToBits_getD s hi

/-- Standard (`Exact`/`Le`) full input parser for
`QCSD_encodeInstance inst ++ QCSD_natToUnary pre.length ++ pre`. -/
abbrev RMParseInputStdQ : Type :=
  RMParsePrefixQ ⊕ (RMReadUnaryQ ⊕ (RMReadUnaryQ ⊕ Bool))

def rmParseInputStd : RMProg EncR RMParseInputStdQ :=
  rmChain rmParsePrefix
    (rmChain (rmReadUnary regCur regT0)
      (rmChain (rmReadUnary regCur regPreLen) (rmCopy regOffPre regCur) false)
      (Sum.inl rmReadUnaryEntry))
    (Sum.inl rmReadUnaryEntry)

def rmParseInputStdEntry : RMParseInputStdQ := Sum.inl rmParsePrefixEntry
def rmParseInputStdExit : RMParseInputStdQ := Sum.inr (Sum.inr (Sum.inr true))

theorem rmParseInputStd_spec (inst : QCSD_Instance) (pre : List Bool)
    (V : ℕ) (reg₀ : RegState EncR)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : (QCSD_encodeInstance inst ++ QCSD_natToUnary pre.length ++ pre).length ≤ V) :
    let inp := QCSD_encodeInstance inst ++ QCSD_natToUnary pre.length ++ pre
    ∃ reg₁ : RegState EncR,
      reg₁ regN = inst.n ∧
      reg₁ regOffH = inst.n + 1 ∧
      reg₁ regOffS = 2 * inst.n + 1 ∧
      reg₁ regT0 = inst.t ∧
      reg₁ regPreLen = pre.length ∧
      reg₁ regOffPre = 3 * inst.n + inst.t + pre.length + 3 ∧
      (∀ (i : ℕ) (hi : i < inst.n), inp.getD (reg₁ regOffH + i) false = decide (inst.h ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      (∀ (i : ℕ) (hi : i < inst.n), inp.getD (reg₁ regOffS + i) false = decide (inst.s ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      (∀ i < pre.length, inp.getD (reg₁ regOffPre + i) false = pre.getD i false) ∧
      RMExec rmParseInputStd V inp rmParseInputStdEntry reg₀ rmParseInputStdExit reg₁ []
        (7 * inst.n + 3 * inst.t + 3 * pre.length + 17) := by
  intro inp
  have hV' : inp.length ≤ V := hV
  have hlen_inp : inp.length = 3 * inst.n + inst.t + 2 * pre.length + 3 := by
    simp only [inp, QCSD_encodeInstance, List.length_append, natToUnary_length, vecToBits_length]
    omega
  have hinp_eq : inp = QCSD_natToUnary inst.n ++ QCSD_vecToBits inst.h ++ QCSD_vecToBits inst.s ++
      (QCSD_natToUnary inst.t ++ QCSD_natToUnary pre.length ++ pre) := by
    simp [inp, QCSD_encodeInstance, List.append_assoc]
  rcases rmParsePrefix_spec inst.h inst.s (QCSD_natToUnary inst.t ++ QCSD_natToUnary pre.length ++ pre)
      V reg₀ hreg₀ (by omega)
    with ⟨r1, h1_n, h1_oH, h1_oS, h1_cur, h1_h, h1_s, hpre⟩
  rw [← hinp_eq] at h1_h h1_s hpre
  set p1 := QCSD_natToUnary inst.n ++ QCSD_vecToBits inst.h ++ QCSD_vecToBits inst.s
  have hp1_len : p1.length = 3 * inst.n + 1 := by
    dsimp only [p1]; rw [List.length_append, List.length_append, natToUnary_length, vecToBits_length, vecToBits_length]; omega
  have hinp1 : inp = p1 ++ QCSD_natToUnary inst.t ++ (QCSD_natToUnary pre.length ++ pre) := by
    simp [inp, p1, QCSD_encodeInstance, List.append_assoc]
  have hrt := rmReadUnary_spec regCur regT0 (by decide) inst.t V inp r1
    (fun j hj => by
      rw [h1_cur, ← hp1_len, hinp1, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt inst.t hj)
    (by
      rw [h1_cur, ← hp1_len, hinp1, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq inst.t)
    hpre.reg₁_le (by rw [h1_cur]; omega) (by omega)
  set r2 := regUpd (regUpd r1 regCur (r1 regCur + inst.t + 1)) regT0 inst.t
  have h2_cur : r2 regCur = 3 * inst.n + inst.t + 2 := by
    dsimp only [r2]; rw [regUpd_ne _ (by decide), regUpd_self, h1_cur]; omega
  set p2 := p1 ++ QCSD_natToUnary inst.t
  have hp2_len : p2.length = 3 * inst.n + inst.t + 2 := by
    dsimp only [p2]; rw [List.length_append, hp1_len, natToUnary_length]; omega
  have hinp2 : inp = p2 ++ QCSD_natToUnary pre.length ++ pre := by
    simp [inp, p2, p1, QCSD_encodeInstance, List.append_assoc]
  have hrp := rmReadUnary_spec regCur regPreLen (by decide) pre.length V inp r2
    (fun j hj => by
      rw [h2_cur, ← hp2_len, hinp2, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt pre.length hj)
    (by
      rw [h2_cur, ← hp2_len, hinp2, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq pre.length)
    hrt.reg₁_le (by rw [h2_cur]; omega) (by omega)
  set r3 := regUpd (regUpd r2 regCur (r2 regCur + pre.length + 1)) regPreLen pre.length
  have h3_cur : r3 regCur = 3 * inst.n + inst.t + pre.length + 3 := by
    dsimp only [r3]; rw [regUpd_ne _ (by decide), regUpd_self, h2_cur]; omega
  have hcp := rmCopy_spec regOffPre regCur V inp r3 hrp.reg₁_le
  set r4 := regUpd r3 regOffPre (r3 regCur)
  have hact_pre : rmParsePrefix rmParsePrefixEntry ≠ none := by
    simp [rmParsePrefix, rmParsePrefixEntry, rmChain, rmSeq, rmZero]
  have hact_ru : ∀ rV : Fin EncR, rmReadUnary regCur rV rmReadUnaryEntry ≠ none := fun rV => by
    simp [rmReadUnary, rmReadUnaryEntry, rmChain, rmSeq, rmZero]
  have hcomb := rmChain_spec_inl hact_pre hpre
    (rmChain_spec_inl (hact_ru regT0) hrt
      (rmChain_spec_inl (hact_ru regPreLen) hrp hcp))
  have hT : 7 * inst.n + 10 + (3 * inst.t + 3 + (3 * pre.length + 3 + 1)) =
      7 * inst.n + 3 * inst.t + 3 * pre.length + 17 := by ring
  rw [max_self, max_self, max_self, List.nil_append, List.nil_append, List.nil_append, hT] at hcomb
  have h4_n : r4 regN = inst.n := by
    dsimp only [r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h1_n]
  have h4_oH : r4 regOffH = inst.n + 1 := by
    dsimp only [r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h1_oH]
  have h4_oS : r4 regOffS = 2 * inst.n + 1 := by
    dsimp only [r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h1_oS]
  have h4_t0 : r4 regT0 = inst.t := by
    dsimp only [r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_self]
  have h4_pl : r4 regPreLen = pre.length := by
    dsimp only [r4, r3]; rw [regUpd_ne _ (by decide), regUpd_self]
  have h4_op : r4 regOffPre = 3 * inst.n + inst.t + pre.length + 3 := by
    dsimp only [r4]; rw [regUpd_self, h3_cur]
  refine ⟨r4, h4_n, h4_oH, h4_oS, h4_t0, h4_pl, h4_op,
    by simpa [h4_oH, h1_oH] using h1_h, by simpa [h4_oS, h1_oS] using h1_s, ?_, hcomb⟩
  intro i hi
  rw [h4_op]
  set p3 := p2 ++ QCSD_natToUnary pre.length
  have hp3_len : p3.length = 3 * inst.n + inst.t + pre.length + 3 := by
    dsimp only [p3]; rw [List.length_append, hp2_len, natToUnary_length]; omega
  rw [← hp3_len, hinp2, list_getD_append_right' p3 pre (by omega)]
  simp

/-- Separate (`Sep`) full input parser for
`QCSD_encodeInstanceSep inst ++ QCSD_natToUnary pre.length ++ pre`. -/
abbrev RMParseInputSepQ : Type :=
  RMParsePrefixQ ⊕ (RMReadUnaryQ ⊕ (RMReadUnaryQ ⊕ (RMReadUnaryQ ⊕ Bool)))

def rmParseInputSep : RMProg EncR RMParseInputSepQ :=
  rmChain rmParsePrefix
    (rmChain (rmReadUnary regCur regT0)
      (rmChain (rmReadUnary regCur regT1)
        (rmChain (rmReadUnary regCur regPreLen) (rmCopy regOffPre regCur) false)
        (Sum.inl rmReadUnaryEntry))
      (Sum.inl rmReadUnaryEntry))
    (Sum.inl rmReadUnaryEntry)

def rmParseInputSepEntry : RMParseInputSepQ := Sum.inl rmParsePrefixEntry
def rmParseInputSepExit : RMParseInputSepQ := Sum.inr (Sum.inr (Sum.inr (Sum.inr true)))

theorem rmParseInputSep_spec (inst : QCSD_InstanceSep) (pre : List Bool)
    (V : ℕ) (reg₀ : RegState EncR)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : (QCSD_encodeInstanceSep inst ++ QCSD_natToUnary pre.length ++ pre).length ≤ V) :
    let inp := QCSD_encodeInstanceSep inst ++ QCSD_natToUnary pre.length ++ pre
    ∃ reg₁ : RegState EncR,
      reg₁ regN = inst.n ∧
      reg₁ regOffH = inst.n + 1 ∧
      reg₁ regOffS = 2 * inst.n + 1 ∧
      reg₁ regT0 = inst.t₀ ∧
      reg₁ regT1 = inst.t₁ ∧
      reg₁ regPreLen = pre.length ∧
      reg₁ regOffPre = 3 * inst.n + inst.t₀ + inst.t₁ + pre.length + 4 ∧
      (∀ (i : ℕ) (hi : i < inst.n), inp.getD (reg₁ regOffH + i) false = decide (inst.h ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      (∀ (i : ℕ) (hi : i < inst.n), inp.getD (reg₁ regOffS + i) false = decide (inst.s ⟨i, hi⟩ = (1 : ZMod 2))) ∧
      (∀ i < pre.length, inp.getD (reg₁ regOffPre + i) false = pre.getD i false) ∧
      RMExec rmParseInputSep V inp rmParseInputSepEntry reg₀ rmParseInputSepExit reg₁ []
        (7 * inst.n + 3 * inst.t₀ + 3 * inst.t₁ + 3 * pre.length + 20) := by
  intro inp
  have hV' : inp.length ≤ V := hV
  have hlen_inp : inp.length = 3 * inst.n + inst.t₀ + inst.t₁ + 2 * pre.length + 4 := by
    simp only [inp, QCSD_encodeInstanceSep, List.length_append, natToUnary_length, vecToBits_length]
    omega
  have hinp_eq : inp = QCSD_natToUnary inst.n ++ QCSD_vecToBits inst.h ++ QCSD_vecToBits inst.s ++
      (QCSD_natToUnary inst.t₀ ++ QCSD_natToUnary inst.t₁ ++ QCSD_natToUnary pre.length ++ pre) := by
    simp [inp, QCSD_encodeInstanceSep, List.append_assoc]
  rcases rmParsePrefix_spec inst.h inst.s
      (QCSD_natToUnary inst.t₀ ++ QCSD_natToUnary inst.t₁ ++ QCSD_natToUnary pre.length ++ pre)
      V reg₀ hreg₀ (by omega)
    with ⟨r1, h1_n, h1_oH, h1_oS, h1_cur, h1_h, h1_s, hpre⟩
  rw [← hinp_eq] at h1_h h1_s hpre
  set p1 := QCSD_natToUnary inst.n ++ QCSD_vecToBits inst.h ++ QCSD_vecToBits inst.s
  have hp1_len : p1.length = 3 * inst.n + 1 := by
    dsimp only [p1]; rw [List.length_append, List.length_append, natToUnary_length, vecToBits_length, vecToBits_length]; omega
  have hinp1 : inp = p1 ++ QCSD_natToUnary inst.t₀ ++
      (QCSD_natToUnary inst.t₁ ++ QCSD_natToUnary pre.length ++ pre) := by
    simp [inp, p1, QCSD_encodeInstanceSep, List.append_assoc]
  have hrt0 := rmReadUnary_spec regCur regT0 (by decide) inst.t₀ V inp r1
    (fun j hj => by
      rw [h1_cur, ← hp1_len, hinp1, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt inst.t₀ hj)
    (by
      rw [h1_cur, ← hp1_len, hinp1, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq inst.t₀)
    hpre.reg₁_le (by rw [h1_cur]; omega) (by omega)
  set r2 := regUpd (regUpd r1 regCur (r1 regCur + inst.t₀ + 1)) regT0 inst.t₀
  have h2_cur : r2 regCur = 3 * inst.n + inst.t₀ + 2 := by
    dsimp only [r2]; rw [regUpd_ne _ (by decide), regUpd_self, h1_cur]; omega
  set p2 := p1 ++ QCSD_natToUnary inst.t₀
  have hp2_len : p2.length = 3 * inst.n + inst.t₀ + 2 := by
    dsimp only [p2]; rw [List.length_append, hp1_len, natToUnary_length]; omega
  have hinp2 : inp = p2 ++ QCSD_natToUnary inst.t₁ ++ (QCSD_natToUnary pre.length ++ pre) := by
    simp [inp, p2, p1, QCSD_encodeInstanceSep, List.append_assoc]
  have hrt1 := rmReadUnary_spec regCur regT1 (by decide) inst.t₁ V inp r2
    (fun j hj => by
      rw [h2_cur, ← hp2_len, hinp2, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt inst.t₁ hj)
    (by
      rw [h2_cur, ← hp2_len, hinp2, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq inst.t₁)
    hrt0.reg₁_le (by rw [h2_cur]; omega) (by omega)
  set r3 := regUpd (regUpd r2 regCur (r2 regCur + inst.t₁ + 1)) regT1 inst.t₁
  have h3_cur : r3 regCur = 3 * inst.n + inst.t₀ + inst.t₁ + 3 := by
    dsimp only [r3]; rw [regUpd_ne _ (by decide), regUpd_self, h2_cur]; omega
  set p3 := p2 ++ QCSD_natToUnary inst.t₁
  have hp3_len : p3.length = 3 * inst.n + inst.t₀ + inst.t₁ + 3 := by
    dsimp only [p3]; rw [List.length_append, hp2_len, natToUnary_length]; omega
  have hinp3 : inp = p3 ++ QCSD_natToUnary pre.length ++ pre := by
    simp [inp, p3, p2, p1, QCSD_encodeInstanceSep, List.append_assoc]
  have hrp := rmReadUnary_spec regCur regPreLen (by decide) pre.length V inp r3
    (fun j hj => by
      rw [h3_cur, ← hp3_len, hinp3, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_lt pre.length hj)
    (by
      rw [h3_cur, ← hp3_len, hinp3, slice_getD_eq _ _ _ (by rw [natToUnary_length]; omega)]
      exact natToUnary_getD_eq pre.length)
    hrt1.reg₁_le (by rw [h3_cur]; omega) (by omega)
  set r4 := regUpd (regUpd r3 regCur (r3 regCur + pre.length + 1)) regPreLen pre.length
  have h4_cur : r4 regCur = 3 * inst.n + inst.t₀ + inst.t₁ + pre.length + 4 := by
    dsimp only [r4]; rw [regUpd_ne _ (by decide), regUpd_self, h3_cur]; omega
  have hcp := rmCopy_spec regOffPre regCur V inp r4 hrp.reg₁_le
  set r5 := regUpd r4 regOffPre (r4 regCur)
  have hact_pre : rmParsePrefix rmParsePrefixEntry ≠ none := by
    simp [rmParsePrefix, rmParsePrefixEntry, rmChain, rmSeq, rmZero]
  have hact_ru : ∀ rV : Fin EncR, rmReadUnary regCur rV rmReadUnaryEntry ≠ none := fun rV => by
    simp [rmReadUnary, rmReadUnaryEntry, rmChain, rmSeq, rmZero]
  have hcomb := rmChain_spec_inl hact_pre hpre
    (rmChain_spec_inl (hact_ru regT0) hrt0
      (rmChain_spec_inl (hact_ru regT1) hrt1
        (rmChain_spec_inl (hact_ru regPreLen) hrp hcp)))
  have hT : 7 * inst.n + 10 + (3 * inst.t₀ + 3 + (3 * inst.t₁ + 3 + (3 * pre.length + 3 + 1))) =
      7 * inst.n + 3 * inst.t₀ + 3 * inst.t₁ + 3 * pre.length + 20 := by ring
  rw [max_self, max_self, max_self, max_self,
      List.nil_append, List.nil_append, List.nil_append, List.nil_append, hT] at hcomb
  have h5_n : r5 regN = inst.n := by
    dsimp only [r5, r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), h1_n]
  have h5_oH : r5 regOffH = inst.n + 1 := by
    dsimp only [r5, r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), h1_oH]
  have h5_oS : r5 regOffS = 2 * inst.n + 1 := by
    dsimp only [r5, r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), h1_oS]
  have h5_t0 : r5 regT0 = inst.t₀ := by
    dsimp only [r5, r4, r3, r2]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_self]
  have h5_t1 : r5 regT1 = inst.t₁ := by
    dsimp only [r5, r4, r3]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_self]
  have h5_pl : r5 regPreLen = pre.length := by
    dsimp only [r5, r4]; rw [regUpd_ne _ (by decide), regUpd_self]
  have h5_op : r5 regOffPre = 3 * inst.n + inst.t₀ + inst.t₁ + pre.length + 4 := by
    dsimp only [r5]; rw [regUpd_self, h4_cur]
  refine ⟨r5, h5_n, h5_oH, h5_oS, h5_t0, h5_t1, h5_pl, h5_op,
    by simpa [h5_oH, h1_oH] using h1_h, by simpa [h5_oS, h1_oS] using h1_s, ?_, hcomb⟩
  intro i hi
  rw [h5_op]
  set p4 := p3 ++ QCSD_natToUnary pre.length
  have hp4_len : p4.length = 3 * inst.n + inst.t₀ + inst.t₁ + pre.length + 4 := by
    dsimp only [p4]; rw [List.length_append, hp3_len, natToUnary_length]; omega
  rw [← hp4_len, hinp3, list_getD_append_right' p4 pre (by omega)]
  simp

/-! ### Exact Copies of `Branch3_Network` Parameter, Offset, and `rawEnds` Definitions -/

def paramK (d : ℕ) : ℕ := minPowExp 9 d
def paramJ (d : ℕ) : ℕ := 3 ^ paramK d
def paramM (d : ℕ) : ℕ := (d + paramJ d - 1) / paramJ d
def paramEll (d : ℕ) : ℕ := minPowExp 3 (2 * paramM d - 1)
def paramL (d : ℕ) : ℕ := 3 ^ paramEll d
def paramL1 (d : ℕ) : ℕ := 3 ^ (paramEll d / 2)
def paramL2 (d : ℕ) : ℕ := 3 ^ ((paramEll d + 1) / 2)
def paramOmegaExp (d : ℕ) : ℕ := 3 ^ (paramK d + 1 - paramEll d)
def paramInvOmegaExp (d : ℕ) : ℕ := 3 * paramJ d - paramOmegaExp d

def treeLog (N_bits : ℕ) : ℕ := max 1 (minPowExp 2 N_bits)
def treeM (N_bits : ℕ) : ℕ := 2 ^ treeLog N_bits

def treeEdgeOff (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 1 => treeEdgeOff r j + (2 * j + 1) * 2 ^ (r - j)

def treeVertOff (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 1 => treeVertOff r j + (j + 1) * 2 ^ (r - j)

def decodeTreeEdgeAux (r rem : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, j => (j, 0, 0)
  | fuel + 1, j =>
    let blk := (2 * j + 1) * 2 ^ (r - j)
    if rem < blk then (j, rem / (2 * j + 1), rem % (2 * j + 1))
    else decodeTreeEdgeAux r (rem - blk) fuel (j + 1)

def decodeTreeEdge (r locE : ℕ) : ℕ × ℕ × ℕ :=
  decodeTreeEdgeAux r locE r 1

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

/-! ### Closed-Form Tree Offset Identities & Linear Bounds for `1 ≤ n` -/

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
    rw [hstep1, hstep2, ih, hexp]; ring

lemma treeEdgeOff_closed_form :
    ∀ r : ℕ, 1 ≤ r → treeEdgeOff r (r + 1) + 2 * r + 5 = 5 * 2 ^ r
  | 0, hr => by omega
  | 1, _ => rfl
  | r + 2, _ => by
    have ih := treeEdgeOff_closed_form (r + 1) (by omega)
    have hstep : treeEdgeOff (r + 2) (r + 3) =
        treeEdgeOff (r + 2) (r + 2) + (2 * (r + 2) + 1) * 2 ^ (r + 2 - (r + 2)) := rfl
    have h2 : treeEdgeOff (r + 2) (r + 2) = 2 * treeEdgeOff (r + 1) (r + 2) :=
      treeEdgeOff_succ_r (r + 1) (r + 2) (Nat.le_refl _)
    have hsub : r + 2 - (r + 2) = 0 := by omega
    have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [pow_succ']
    have h12 : r + 1 + 1 = r + 2 := by omega
    rw [h12] at ih
    rw [hstep, h2, hsub, pow_zero, Nat.mul_one, hpow]; omega

lemma treeVertOff_succ_r (r : ℕ) :
    ∀ k : ℕ, k ≤ r + 1 → treeVertOff (r + 1) k = 2 * treeVertOff r k
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hj => by
    have ih := treeVertOff_succ_r r (j + 1) (by omega)
    have hstep1 : treeVertOff (r + 1) (j + 2) =
        treeVertOff (r + 1) (j + 1) + ((j + 1) + 1) * 2 ^ (r + 1 - (j + 1)) := rfl
    have hstep2 : treeVertOff r (j + 2) =
        treeVertOff r (j + 1) + ((j + 1) + 1) * 2 ^ (r - (j + 1)) := rfl
    have hexp : 2 ^ (r + 1 - (j + 1)) = 2 * 2 ^ (r - (j + 1)) := by
      have : r + 1 - (j + 1) = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']
    rw [hstep1, hstep2, ih, hexp]; ring

lemma treeVertOff_closed_form :
    ∀ r : ℕ, 1 ≤ r → treeVertOff r (r + 1) + r + 3 = 3 * 2 ^ r
  | 0, hr => by omega
  | 1, _ => rfl
  | r + 2, _ => by
    have ih := treeVertOff_closed_form (r + 1) (by omega)
    have hstep : treeVertOff (r + 2) (r + 3) =
        treeVertOff (r + 2) (r + 2) + ((r + 2) + 1) * 2 ^ (r + 2 - (r + 2)) := rfl
    have h2 : treeVertOff (r + 2) (r + 2) = 2 * treeVertOff (r + 1) (r + 2) :=
      treeVertOff_succ_r (r + 1) (r + 2) (Nat.le_refl _)
    have hsub : r + 2 - (r + 2) = 0 := by omega
    have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [pow_succ']
    have h12 : r + 1 + 1 = r + 2 := by omega
    rw [h12] at ih
    rw [hstep, h2, hsub, pow_zero, Nat.mul_one, hpow]; omega

lemma treeVertOff_net (n : ℕ) :
    treeVertOff (treeLog n + 1) (treeLog n + 2) = 6 * treeM n - (treeLog n + 4) := by
  have h := treeVertOff_closed_form (treeLog n + 1) (by omega)
  have hpow : 2 ^ (treeLog n + 1) = 2 * treeM n := by unfold treeM; rw [pow_succ']
  have h2 : treeLog n + 1 + 1 = treeLog n + 2 := by omega
  rw [hpow, h2] at h; omega

lemma treeEdgeOff_net (n : ℕ) :
    treeEdgeOff (treeLog n + 1) (treeLog n + 2) = 10 * treeM n - (2 * treeLog n + 7) := by
  have h := treeEdgeOff_closed_form (treeLog n + 1) (by omega)
  have hpow : 2 ^ (treeLog n + 1) = 2 * treeM n := by unfold treeM; rw [pow_succ']
  have h2 : treeLog n + 1 + 1 = treeLog n + 2 := by omega
  rw [hpow, h2] at h; omega

lemma paramJ_sq_eq (d : ℕ) : (paramJ d) ^ 2 = 9 ^ paramK d := by
  unfold paramJ
  calc (3 ^ paramK d) ^ 2 = (3 ^ 2) ^ paramK d := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 9 ^ paramK d := by norm_num

lemma one_le_paramJ (d : ℕ) : 1 ≤ paramJ d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_paramL (d : ℕ) : 1 ≤ paramL d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_paramL1 (d : ℕ) : 1 ≤ paramL1 d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_paramL2 (d : ℕ) : 1 ≤ paramL2 d := Nat.one_le_pow _ 3 (by decide)

lemma paramJ_sq_lt_nine_mul {d : ℕ} (hd : 1 ≤ d) : (paramJ d) ^ 2 < 9 * d := by
  rw [paramJ_sq_eq]
  rcases Nat.eq_zero_or_pos (paramK d) with hk0 | hkpos
  · rw [hk0]; simp; omega
  · have hlt : 9 ^ (paramK d - 1) < d := lt_of_lt_minPowExp (by decide) (show paramK d - 1 < minPowExp 9 d by unfold paramK at hkpos ⊢; omega)
    have hpow : 9 ^ paramK d = 9 * 9 ^ (paramK d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hkpos, pow_succ']
    omega

lemma paramM_le_paramJ {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ paramJ d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hdJ : d ≤ (paramJ d) ^ 2 := by rw [paramJ_sq_eq]; exact minPowExp_le_pow (by decide) d
  have hlt : d + paramJ d - 1 < (paramJ d + 1) * paramJ d := by
    have : (paramJ d + 1) * paramJ d = (paramJ d) ^ 2 + paramJ d := by ring
    omega
  have := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  omega

lemma paramM_le_self {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hlt : d + paramJ d - 1 < (d + 1) * paramJ d := by
    have : (d + 1) * paramJ d = d * paramJ d + paramJ d := by ring
    have : d ≤ d * paramJ d := Nat.le_mul_of_pos_right d hJ
    omega
  have := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  omega

lemma paramEll_le_paramK_succ {d : ℕ} (hd : 1 ≤ d) : paramEll d ≤ paramK d + 1 := by
  apply minPowExp_min (by decide)
  have hm := paramM_le_paramJ hd
  have hJ := one_le_paramJ d
  have hpow : 3 ^ (paramK d + 1) = 3 * paramJ d := by unfold paramJ; rw [pow_succ']
  omega

lemma paramL_le_three_mul_paramJ {d : ℕ} (hd : 1 ≤ d) : paramL d ≤ 3 * paramJ d := by
  calc paramL d = 3 ^ paramEll d := rfl
    _ ≤ 3 ^ (paramK d + 1) := Nat.pow_le_pow_right (by decide) (paramEll_le_paramK_succ hd)
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma paramL1_le_paramL (d : ℕ) : paramL1 d ≤ paramL d :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)

lemma paramL2_le_paramL (d : ℕ) : paramL2 d ≤ paramL d := by
  unfold paramL2 paramL
  rcases Nat.eq_zero_or_pos (paramEll d) with h0 | hpos
  · simp [h0]
  · exact Nat.pow_le_pow_right (by decide) (by omega)

lemma paramJ_le_nine_mul {d : ℕ} (hd : 1 ≤ d) : paramJ d ≤ 9 * d := by
  have h1 := one_le_paramJ d
  have h2 := paramJ_sq_lt_nine_mul hd
  have h3 : paramJ d ≤ (paramJ d) ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_left _ h1
  omega

lemma two_J_L_lt {d : ℕ} (hd : 1 ≤ d) : 2 * paramJ d * paramL d < 54 * d := by
  have hL := paramL_le_three_mul_paramJ hd
  have hJ2 := paramJ_sq_lt_nine_mul hd
  calc 2 * paramJ d * paramL d ≤ 2 * paramJ d * (3 * paramJ d) := Nat.mul_le_mul_left _ hL
    _ = 6 * (paramJ d) ^ 2 := by ring
    _ < 6 * (9 * d) := Nat.mul_lt_mul_of_pos_left hJ2 (by decide)
    _ = 54 * d := by ring

lemma paramL_le_27_mul {d : ℕ} (hd : 1 ≤ d) : paramL d ≤ 27 * d := by
  have h1 := paramL_le_three_mul_paramJ hd
  have h2 := paramJ_le_nine_mul hd
  omega

lemma paramOmegaExp_le (d : ℕ) : paramOmegaExp d ≤ 3 * paramJ d := by
  unfold paramOmegaExp
  calc 3 ^ (paramK d + 1 - paramEll d) ≤ 3 ^ (paramK d + 1) :=
        Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma le_treeM (n : ℕ) : n ≤ treeM n := by
  unfold treeM treeLog
  exact le_trans (minPowExp_le_pow (by decide) n)
    (Nat.pow_le_pow_right (by decide) (le_max_right 1 _))

lemma treeM_le_two_mul {n : ℕ} (hn : 1 ≤ n) : treeM n ≤ 2 * n := by
  unfold treeM treeLog
  by_cases hn1 : n = 1
  · subst hn1; decide
  · have h2 : 2 ≤ n := by omega
    have hm1 : 1 ≤ minPowExp 2 n := by
      by_contra h0
      have h0' : minPowExp 2 n = 0 := by omega
      have hle := minPowExp_le_pow (b := 2) (by decide) n
      rw [h0'] at hle; omega
    rw [max_eq_right hm1]
    have hlt : 2 ^ (minPowExp 2 n - 1) < n := lt_of_lt_minPowExp (by decide) (by omega)
    have hpow : 2 ^ minPowExp 2 n = 2 * 2 ^ (minPowExp 2 n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
    omega

lemma treeLog_le_self {n : ℕ} (hn : 1 ≤ n) : treeLog n ≤ n := by
  unfold treeLog
  exact max_le hn (minPowExp_le_self (by decide) n)

lemma netVertCount_le {n : ℕ} (hn : 1 ≤ n) : netVertCount n ≤ 500 * n + 20 := by
  have hL := paramL_le_27_mul hn
  have hL1 := paramL1_le_paramL n
  have hL2 := paramL2_le_paramL n
  have h2JL := two_J_L_lt hn
  have hM := treeM_le_two_mul hn
  have hlog := treeLog_le_self hn
  have hv := treeVertOff_net n
  simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
    netV10, netV9, netV8, netV7, hv]
  omega

lemma netEdgeCount_le {n : ℕ} (hn : 1 ≤ n) : netEdgeCount n ≤ 500 * n + 20 := by
  have h2JL := two_J_L_lt hn
  have hM := treeM_le_two_mul hn
  have hlog := treeLog_le_self hn
  have he := treeEdgeOff_net n
  simp only [netEdgeCount, netE13, netE12, netE11, netE10, netE9, netE8, netE7, netE6,
    netE5, netE4, netE3, he]
  omega

/-! ### Parameter Computation Macro (`rmComputeParams`) -/

/-- Predicate asserting that all 34 parameter & offset registers hold their exact values for `n`. -/
def ParamsLoaded (n : ℕ) (reg : RegState EncR) : Prop :=
  reg regN = n ∧
  reg regK = paramK n ∧
  reg regJ = paramJ n ∧
  reg regM = paramM n ∧
  reg regEll = paramEll n ∧
  reg regL = paramL n ∧
  reg regL1 = paramL1 n ∧
  reg regL2 = paramL2 n ∧
  reg regOmega = paramOmegaExp n ∧
  reg regInvOmega = paramInvOmegaExp n ∧
  reg regTreeLog = treeLog n ∧
  reg regTreeM = treeM n ∧
  reg regVertCount = netVertCount n ∧
  reg regEdgeCount = netEdgeCount n ∧
  reg regV1 = netV1 n ∧ reg regV2 = netV2 n ∧ reg regV3 = netV3 n ∧
  reg regV4 = netV4 n ∧ reg regV5 = netV5 n ∧ reg regV6 = netV6 n ∧
  reg regV7 = netV7 n ∧ reg regV8 = netV8 n ∧ reg regV9 = netV9 n ∧
  reg regV10 = netV10 n ∧ reg regV11 = netV11 n ∧ reg regV12 = netV12 n ∧
  reg regV13 = netV13 n ∧ reg regV14 = netV14 n ∧ reg regV15 = netV15 n ∧
  reg regV16 = netV16 n ∧ reg regV17 = netV17 n ∧ reg regV18 = netV18 n ∧
  reg regTwoJ = 2 * paramJ n ∧
  reg regTwoJL = 2 * paramJ n * paramL n

/-- Phase A1: computes `K, J, M, Ell, L` from `regN = n`. -/
abbrev RMParamsA1Q : Type :=
  RMSetConstQ 9 ⊕ (RMMinPowExpQ ⊕ (RMSetConstQ 3 ⊕ (RMPowQ ⊕
    (Bool ⊕ (RMAddQ ⊕ (Bool ⊕ (RMDivModQ ⊕
      (Bool ⊕ (RMAddQ ⊕ (Bool ⊕ (RMSetConstQ 3 ⊕ RMMinPowExpQ)))))))))))

def rmParamsA1 : RMProg EncR RMParamsA1Q :=
  rmChain (rmSetConst regS0 9)
    (rmChain (rmMinPowExp regK regS0 regN regS1 regS2 regS3 regS4 regS5)
      (rmChain (rmSetConst regS0 3)
        (rmChain (rmPow regJ regS0 regK regS1 regS2 regS3 regS4)
          (rmChain (rmCopy regS0 regN)
            (rmChain (rmAdd regS0 regJ regS1)
              (rmChain (rmDec1 regS0)
                (rmChain (rmDivMod regM regS1 regS0 regJ regS2 regS3 regS4)
                  (rmChain (rmCopy regS0 regM)
                    (rmChain (rmAdd regS0 regM regS1)
                      (rmChain (rmDec1 regS0)
                        (rmChain (rmSetConst regS7 3)
                          (rmMinPowExp regEll regS7 regS0 regL regS2 regS3 regS4 regS5)
                          rmMinPowExpEntry)
                        (Sum.inl rmSetConstEntry))
                      (Sum.inl false))
                    (Sum.inl rmAddEntry))
                  (Sum.inl false))
                (Sum.inl rmDivModEntry))
              (Sum.inl false))
            (Sum.inl rmAddEntry))
          (Sum.inl false))
        (Sum.inl rmPowEntry))
      (Sum.inl rmSetConstEntry))
    (Sum.inl rmMinPowExpEntry)

def rmParamsA1Entry : RMParamsA1Q := Sum.inl rmSetConstEntry
def rmParamsA1Exit : RMParamsA1Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr rmMinPowExpExit)))))))))))

lemma rmParamsA1_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hN : reg₀ regN = n) (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      reg₁ regN = n ∧ reg₁ regK = paramK n ∧ reg₁ regJ = paramJ n ∧
      reg₁ regM = paramM n ∧ reg₁ regEll = paramEll n ∧ reg₁ regL = paramL n ∧
      (∀ i, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec rmParamsA1 V inp rmParamsA1Entry reg₀ rmParamsA1Exit reg₁ []
        (100 * n * V + 200 * n ^ 2 + 500 * n + 200) := by
  have h1V : 1 ≤ V := by omega
  have hK_le : paramK n ≤ n := minPowExp_le_self (by decide) n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hM_le : paramM n ≤ n := paramM_le_self hn
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  -- 1. S0 := 9
  have hs1 := rmSetConst_spec regS0 9 V inp reg₀ hreg₀ (by omega)
  set r1 := regUpd reg₀ regS0 9
  -- 2. K := minPowExp 9 n
  rcases rmMinPowExp_spec regK regS0 regN regS1 regS2 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r1 (by simp [r1]) hs1.reg₁_le h1V (by simp [r1, hN]; omega)
    with ⟨r2, h2_K, _, h2_fr, he2⟩
  have h2_N : r2 regN = n := by
    rw [h2_fr regN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r1, hN]
  have h2_K' : r2 regK = paramK n := by simpa [r1, hN, paramK] using h2_K
  -- 3. S0 := 3
  have hs3 := rmSetConst_spec regS0 3 V inp r2 he2.reg₁_le (by omega)
  set r3 := regUpd r2 regS0 3
  -- 4. J := 3 ^ K
  rcases rmPow_spec regJ regS0 regK regS1 regS2 regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r3 hs3.reg₁_le h1V (by simp [r3, h2_K']; change paramJ n ≤ V; omega)
    with ⟨r4, h4_J, h4_fr, he4⟩
  have h4_N : r4 regN = n := by
    rw [h4_fr regN (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r3, h2_N]
  have h4_K : r4 regK = paramK n := by
    rw [h4_fr regK (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r3, h2_K']
  have h4_J' : r4 regJ = paramJ n := by simpa [r3, h2_K', paramJ] using h4_J
  -- 5. S0 := N; S0 += J; dec1 S0
  have hc5 := rmCopy_spec regS0 regN V inp r4 he4.reg₁_le
  set r5 := regUpd r4 regS0 (r4 regN)
  have ha6 := rmAdd_spec regS0 regJ regS1 (by decide) (by decide) V inp r5 hc5.reg₁_le
    (by dsimp only [r5]; rw [regUpd_self, regUpd_ne _ (by decide), h4_N, h4_J']; omega)
  set r6 := regUpd (regUpd r5 regS0 (r5 regS0 + r5 regJ)) regS1 0
  have hd7 := rmDec1_spec regS0 V inp r6 ha6.reg₁_le
  set r7 := regUpd r6 regS0 (r6 regS0 - 1)
  have h7_S0 : r7 regS0 = n + paramJ n - 1 := by
    dsimp only [r7, r6, r5]
    rw [regUpd_self, regUpd_ne _ (by decide), regUpd_self, regUpd_self, regUpd_ne _ (by decide), h4_N, h4_J']
  have h7_J : r7 regJ = paramJ n := by
    dsimp only [r7, r6, r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h4_J']
  have h7_N : r7 regN = n := by
    dsimp only [r7, r6, r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h4_N]
  have h7_K : r7 regK = paramK n := by
    dsimp only [r7, r6, r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h4_K]
  -- 6. M := S0 / J
  rcases rmDivMod_spec regM regS1 regS0 regJ regS2 regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp r7 (by rw [h7_J]; exact hJ_pos) hd7.reg₁_le h1V
    with ⟨r8, h8_M, _, h8_fr, he8⟩
  have h8_M' : r8 regM = paramM n := by rw [h8_M, h7_S0, h7_J]; rfl
  have h8_N : r8 regN = n := by rw [h8_fr regN (by decide) (by decide) (by decide) (by decide) (by decide), h7_N]
  have h8_K : r8 regK = paramK n := by rw [h8_fr regK (by decide) (by decide) (by decide) (by decide) (by decide), h7_K]
  have h8_J : r8 regJ = paramJ n := by rw [h8_fr regJ (by decide) (by decide) (by decide) (by decide) (by decide), h7_J]
  -- 7. S0 := M; S0 += M; dec1 S0; S7 := 3; (Ell, L) := minPowExp 3 (2M - 1)
  have hc9 := rmCopy_spec regS0 regM V inp r8 he8.reg₁_le
  set r9 := regUpd r8 regS0 (r8 regM)
  have ha10 := rmAdd_spec regS0 regM regS1 (by decide) (by decide) V inp r9 hc9.reg₁_le
    (by dsimp only [r9]; rw [regUpd_self, regUpd_ne _ (by decide), h8_M']; omega)
  set r10 := regUpd (regUpd r9 regS0 (r9 regS0 + r9 regM)) regS1 0
  have hd11 := rmDec1_spec regS0 V inp r10 ha10.reg₁_le
  set r11 := regUpd r10 regS0 (r10 regS0 - 1)
  have hs12 := rmSetConst_spec regS7 3 V inp r11 hd11.reg₁_le (by omega)
  set r12 := regUpd r11 regS7 3
  have h12_S0 : r12 regS0 = 2 * paramM n - 1 := by
    dsimp only [r12, r11, r10, r9]
    rw [regUpd_ne _ (by decide), regUpd_self, regUpd_ne _ (by decide), regUpd_self, regUpd_self,
        regUpd_ne _ (by decide), h8_M']
    omega
  have h12_S7 : r12 regS7 = 3 := regUpd_self _ _ _
  rcases rmMinPowExp_spec regEll regS7 regS0 regL regS2 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r12 (by rw [h12_S7]; decide) hs12.reg₁_le h1V (by rw [h12_S7, h12_S0]; omega)
    with ⟨r13, h13_Ell, h13_L, h13_fr, he13⟩
  have h13_Ell' : r13 regEll = paramEll n := by rw [h13_Ell, h12_S7, h12_S0]; rfl
  have h13_L' : r13 regL = paramL n := by rw [h13_L, h12_S7, h12_S0]; rfl
  have hframe_gen : ∀ i : Fin EncR,
      i ≠ regK → i ≠ regJ → i ≠ regM → i ≠ regEll → i ≠ regL →
      i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → i ≠ regS5 → i ≠ regS7 →
      r13 i = reg₀ i := by
    intro i hiK hiJ hiM hiE hiL hi0 hi1 hi2 hi3 hi4 hi5 hi7
    rw [h13_fr i hiE hiL hi2 hi3 hi4 hi5]
    dsimp only [r12, r11, r10, r9]
    rw [regUpd_ne _ hi7, regUpd_ne _ hi0, regUpd_ne _ hi1, regUpd_ne _ hi0, regUpd_ne _ hi0]
    rw [h8_fr i hiM hi1 hi2 hi3 hi4]
    dsimp only [r7, r6, r5]
    rw [regUpd_ne _ hi0, regUpd_ne _ hi1, regUpd_ne _ hi0, regUpd_ne _ hi0]
    rw [h4_fr i hiJ hi1 hi2 hi3 hi4]
    dsimp only [r3]
    rw [regUpd_ne _ hi0, h2_fr i hiK hi1 hi2 hi3 hi4 hi5]
    dsimp only [r1]
    rw [regUpd_ne _ hi0]
  have h13_N : r13 regN = n := by
    rw [hframe_gen regN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hN]
  have h13_K : r13 regK = paramK n := by
    rw [h13_fr regK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r12, r11, r10, r9]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h8_K]
  have h13_J : r13 regJ = paramJ n := by
    rw [h13_fr regJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r12, r11, r10, r9]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h8_J]
  have h13_M : r13 regM = paramM n := by
    rw [h13_fr regM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r12, r11, r10, r9]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h8_M']
  -- Chain all 13 steps
  have hact_sc : ∀ (r : Fin EncR) (c : ℕ), rmSetConst r c rmSetConstEntry ≠ none := fun _ _ => by
    simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]
  have hact_mp : ∀ (a b c d e f g h : Fin EncR), rmMinPowExp a b c d e f g h rmMinPowExpEntry ≠ none := by
    intros; simp [rmMinPowExp, rmMinPowExpEntry, rmChain, rmSeq, rmZero]
  have hact_pow : ∀ (a b c d e f g : Fin EncR), rmPow a b c d e f g rmPowEntry ≠ none := by
    intros; simp [rmPow, rmPowEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hact_add : ∀ (a b c : Fin EncR), rmAdd a b c rmAddEntry ≠ none := by
    intros; simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]
  have hact_div : ∀ (a b c d e f g : Fin EncR), rmDivMod a b c d e f g rmDivModEntry ≠ none := by
    intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
  have hchain :=
    rmChain_spec_inl (hact_sc _ _) hs1
      (rmChain_spec_inl (hact_mp _ _ _ _ _ _ _ _) he2
        (rmChain_spec_inl (hact_sc _ _) hs3
          (rmChain_spec_inl (hact_pow _ _ _ _ _ _ _) he4
            (rmChain_spec_inl (by simp [rmCopy]) hc5
              (rmChain_spec_inl (hact_add _ _ _) ha6
                (rmChain_spec_inl (by simp [rmDec1]) hd7
                  (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) he8
                    (rmChain_spec_inl (by simp [rmCopy]) hc9
                      (rmChain_spec_inl (hact_add _ _ _) ha10
                        (rmChain_spec_inl (by simp [rmDec1]) hd11
                          (rmChain_spec_inl (hact_sc _ _) hs12 he13)))))))))))
  have hT_le :
      (1 + 9) + ((r1 regN * (r1 regN * (2 * r1 regS0 + 5) + 15) + 11) +
        ((1 + 3) + ((r3 regK * (V * (2 * r3 regS0 + 3) + 5) + 4) +
          (1 + ((2 * r5 regJ + 2) + (1 + ((15 * r7 regS0 + 2 * r7 regJ + 10) +
            (1 + ((2 * r9 regM + 2) + (1 + ((1 + 3) +
              (r12 regS0 * (r12 regS0 * (2 * r12 regS7 + 5) + 15) + 11)))))))))))) ≤
      100 * n * V + 200 * n ^ 2 + 500 * n + 200 := by
    have hr1N : r1 regN = n := by dsimp only [r1]; rw [regUpd_ne _ (by decide), hN]
    have hr1S0 : r1 regS0 = 9 := regUpd_self _ _ _
    have hr3K : r3 regK = paramK n := by dsimp only [r3]; rw [regUpd_ne _ (by decide), h2_K']
    have hr3S0 : r3 regS0 = 3 := regUpd_self _ _ _
    have hr5J : r5 regJ = paramJ n := by dsimp only [r5]; rw [regUpd_ne _ (by decide), h4_J']
    have hr9M : r9 regM = paramM n := by dsimp only [r9]; rw [regUpd_ne _ (by decide), h8_M']
    rw [hr1N, hr1S0, hr3K, hr3S0, hr5J, h7_S0, h7_J, hr9M, h12_S0, h12_S7]
    have ht1 : paramK n * (V * 9 + 5) ≤ n * (V * 9 + 5) := Nat.mul_le_mul_right _ hK_le
    have ht2 : (2 * paramM n - 1) * ((2 * paramM n - 1) * 11 + 15) ≤
        (2 * n) * ((2 * n) * 11 + 15) := by
      have hm2 : 2 * paramM n - 1 ≤ 2 * n := by omega
      exact Nat.mul_le_mul hm2 (by omega)
    have hsq1 : n * (n * (2 * 9 + 5) + 15) = 23 * n ^ 2 + 15 * n := by ring
    have hsq2 : (2 * n) * ((2 * n) * 11 + 15) = 44 * n ^ 2 + 30 * n := by ring
    have hmulV : n * (V * 9 + 5) = 9 * (n * V) + 5 * n := by ring
    have h100 : 100 * n * V = 100 * (n * V) := by ring
    have h9 : V * (2 * 3 + 3) + 5 = V * 9 + 5 := by ring
    have h11 : (2 * 3 + 5) = 11 := rfl
    rw [hmulV] at ht1
    rw [hsq2] at ht2
    rw [h9, h11, hsq1, h100]
    have hfin : ∀ a b c d e : ℕ,
        a ≤ 9 * (n * V) + 5 * n →
        b ≤ 44 * n ^ 2 + 30 * n →
        c ≤ n + d →
        d ≤ 9 * n →
        e ≤ n →
        1 + 9 + (23 * n ^ 2 + 15 * n + 11 + (1 + 3 + (a + 4 + (1 + (2 * d + 2 +
          (1 + (15 * c + 2 * d + 10 + (1 + (2 * e + 2 + (1 + (1 + 3 + (b + 11)))))))))))) ≤
          100 * (n * V) + 200 * n ^ 2 + 500 * n + 200 := by
      intros; omega
    exact hfin _ _ _ _ _ ht1 ht2 (Nat.sub_le _ _) hJ_le hM_le
  have hfinal := hchain.weaken (V₂ := V) (T₂ := 100 * n * V + 200 * n ^ 2 + 500 * n + 200)
    (by simp) hT_le
  simp only [List.nil_append] at hfinal
  refine ⟨r13, h13_N, h13_K, h13_J, h13_M, h13_Ell', h13_L', ?_, hfinal⟩
  intro i hi1 hi2
  exact hframe_gen i
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)

/-- Phase A2: computes `L1, L2, Omega, InvOmega, TwoJ, TwoJL` from `K, J, Ell, L`. -/
abbrev RMParamsA2Q : Type :=
  RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (RMSetConstQ 3 ⊕ (RMPowQ ⊕
    (Bool ⊕ (Bool ⊕ (RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (RMSetConstQ 3 ⊕ (RMPowQ ⊕
      (Bool ⊕ (Bool ⊕ (RMSubQ ⊕ (RMSetConstQ 3 ⊕ (RMPowQ ⊕
        (RMSetConstQ 3 ⊕ (RMMulQ ⊕ (RMSubQ ⊕ (Bool ⊕ (RMAddQ ⊕ RMMulQ)))))))))))))))))))

def rmParamsA2 : RMProg EncR RMParamsA2Q :=
  rmChain (rmSetConst regS0 2)
    (rmChain (rmDivMod regS1 regS2 regEll regS0 regS3 regS4 regS5)
      (rmChain (rmSetConst regS7 3)
        (rmChain (rmPow regL1 regS7 regS1 regS2 regS3 regS4 regS5)
          (rmChain (rmCopy regS6 regEll)
            (rmChain (rmInc regS6)
              (rmChain (rmSetConst regS0 2)
                (rmChain (rmDivMod regS1 regS2 regS6 regS0 regS3 regS4 regS5)
                  (rmChain (rmSetConst regS7 3)
                    (rmChain (rmPow regL2 regS7 regS1 regS2 regS3 regS4 regS5)
                      (rmChain (rmCopy regS6 regK)
                        (rmChain (rmInc regS6)
                          (rmChain (rmSub regS6 regEll regS1)
                            (rmChain (rmSetConst regS7 3)
                              (rmChain (rmPow regOmega regS7 regS6 regS1 regS2 regS3 regS4)
                                (rmChain (rmSetConst regS0 3)
                                  (rmChain (rmMul regInvOmega regS0 regJ regS1 regS2)
                                    (rmChain (rmSub regInvOmega regOmega regS1)
                                      (rmChain (rmCopy regTwoJ regJ)
                                        (rmChain (rmAdd regTwoJ regJ regS1)
                                          (rmMul regTwoJL regTwoJ regL regS1 regS2)
                                          rmMulEntry)
                                        (Sum.inl rmAddEntry))
                                      (Sum.inl false))
                                    (Sum.inl rmSubEntry))
                                  (Sum.inl rmMulEntry))
                                (Sum.inl rmSetConstEntry))
                              (Sum.inl rmPowEntry))
                            (Sum.inl rmSetConstEntry))
                          (Sum.inl rmSubEntry))
                        (Sum.inl false))
                      (Sum.inl false))
                    (Sum.inl rmPowEntry))
                  (Sum.inl rmSetConstEntry))
                (Sum.inl rmDivModEntry))
              (Sum.inl rmSetConstEntry))
            (Sum.inl false))
          (Sum.inl false))
        (Sum.inl rmPowEntry))
      (Sum.inl rmSetConstEntry))
    (Sum.inl rmDivModEntry)

def rmParamsA2Entry : RMParamsA2Q := Sum.inl rmSetConstEntry
def rmParamsA2Exit : RMParamsA2Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr rmMulExit)))))))))))))))))))

lemma rmParamsA2_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n)
    (hN : reg₀ regN = n) (hK : reg₀ regK = paramK n) (hJ : reg₀ regJ = paramJ n)
    (hM : reg₀ regM = paramM n) (hEll : reg₀ regEll = paramEll n) (hL : reg₀ regL = paramL n)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      reg₁ regN = n ∧ reg₁ regK = paramK n ∧ reg₁ regJ = paramJ n ∧
      reg₁ regM = paramM n ∧ reg₁ regEll = paramEll n ∧ reg₁ regL = paramL n ∧
      reg₁ regL1 = paramL1 n ∧ reg₁ regL2 = paramL2 n ∧
      reg₁ regOmega = paramOmegaExp n ∧ reg₁ regInvOmega = paramInvOmegaExp n ∧
      reg₁ regTwoJ = 2 * paramJ n ∧ reg₁ regTwoJL = 2 * paramJ n * paramL n ∧
      (∀ i, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec rmParamsA2 V inp rmParamsA2Entry reg₀ rmParamsA2Exit reg₁ []
        (100 * n * V + 2000 * n ^ 2 + 1000 * n + 200) := by
  have h1V : 1 ≤ V := by omega
  have hK_le : paramK n ≤ n := minPowExp_le_self (by decide) n
  have hEll_le : paramEll n ≤ n + 1 := by
    have := paramEll_le_paramK_succ hn; omega
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hL1_le : paramL1 n ≤ 27 * n := le_trans (paramL1_le_paramL n) hL_le
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) hL_le
  have hOm_le : paramOmegaExp n ≤ 27 * n := le_trans (paramOmegaExp_le n) (by omega)
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  -- L1 = 3 ^ (Ell / 2)
  have e1 := rmSetConst_spec regS0 2 V inp reg₀ hreg₀ (by omega)
  set r1 := regUpd reg₀ regS0 2
  rcases rmDivMod_spec regS1 regS2 regEll regS0 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp r1 (by simp [r1]) e1.reg₁_le h1V
    with ⟨r2, h2_q, _, h2_fr, e2⟩
  have h2_S1 : r2 regS1 = paramEll n / 2 := by
    rw [h2_q]; simp [r1, hEll]
  have e3 := rmSetConst_spec regS7 3 V inp r2 e2.reg₁_le (by omega)
  set r3 := regUpd r2 regS7 3
  rcases rmPow_spec regL1 regS7 regS1 regS2 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r3 e3.reg₁_le h1V (by simp [r3, h2_S1]; change paramL1 n ≤ V; omega)
    with ⟨r4, h4_L1, h4_fr, e4⟩
  have h4_L1' : r4 regL1 = paramL1 n := by simpa [r3, h2_S1, paramL1] using h4_L1
  have h4_Ell : r4 regEll = paramEll n := by
    rw [h4_fr regEll (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r3]; rw [regUpd_ne _ (by decide),
      h2_fr regEll (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [r1, hEll]
  -- L2 = 3 ^ ((Ell + 1) / 2)
  have e5 := rmCopy_spec regS6 regEll V inp r4 e4.reg₁_le
  set r5 := regUpd r4 regS6 (r4 regEll)
  have e6 := rmInc_spec regS6 V inp r5 e5.reg₁_le (by dsimp only [r5]; rw [regUpd_self, h4_Ell]; omega)
  set r6 := regUpd r5 regS6 (r5 regS6 + 1)
  have e7 := rmSetConst_spec regS0 2 V inp r6 e6.reg₁_le (by omega)
  set r7 := regUpd r6 regS0 2
  have h7_S6 : r7 regS6 = paramEll n + 1 := by
    dsimp only [r7, r6, r5]; rw [regUpd_ne _ (by decide), regUpd_self, regUpd_self, h4_Ell]
  rcases rmDivMod_spec regS1 regS2 regS6 regS0 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp r7 (by simp [r7]) e7.reg₁_le h1V
    with ⟨r8, h8_q, _, h8_fr, e8⟩
  have h8_S1 : r8 regS1 = (paramEll n + 1) / 2 := by rw [h8_q, h7_S6]; simp [r7]
  have e9 := rmSetConst_spec regS7 3 V inp r8 e8.reg₁_le (by omega)
  set r9 := regUpd r8 regS7 3
  rcases rmPow_spec regL2 regS7 regS1 regS2 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r9 e9.reg₁_le h1V (by simp [r9, h8_S1]; change paramL2 n ≤ V; omega)
    with ⟨r10, h10_L2, h10_fr, e10⟩
  have h10_L2' : r10 regL2 = paramL2 n := by simpa [r9, h8_S1, paramL2] using h10_L2
  have h10_keep : ∀ i : Fin EncR,
      i ≠ regL1 → i ≠ regL2 → i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 →
      i ≠ regS4 → i ≠ regS5 → i ≠ regS6 → i ≠ regS7 → r10 i = reg₀ i := by
    intro i hL1i hL2i h0 h1 h2 h3 h4 h5 h6 h7
    rw [h10_fr i hL2i h2 h3 h4 h5]
    dsimp only [r9]; rw [regUpd_ne _ h7, h8_fr i h1 h2 h3 h4 h5]
    dsimp only [r7, r6, r5]; rw [regUpd_ne _ h0, regUpd_ne _ h6, regUpd_ne _ h6]
    rw [h4_fr i hL1i h2 h3 h4 h5]
    dsimp only [r3]; rw [regUpd_ne _ h7, h2_fr i h1 h2 h3 h4 h5]
    dsimp only [r1]; rw [regUpd_ne _ h0]
  have h10_K : r10 regK = paramK n := by
    rw [h10_keep regK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hK]
  have h10_Ell : r10 regEll = paramEll n := by
    rw [h10_keep regEll (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hEll]
  -- Omega = 3 ^ (K + 1 - Ell)
  have e11 := rmCopy_spec regS6 regK V inp r10 e10.reg₁_le
  set r11 := regUpd r10 regS6 (r10 regK)
  have e12 := rmInc_spec regS6 V inp r11 e11.reg₁_le (by dsimp only [r11]; rw [regUpd_self, h10_K]; omega)
  set r12 := regUpd r11 regS6 (r11 regS6 + 1)
  have e13 := rmSub_spec regS6 regEll regS1 (by decide) V inp r12 e12.reg₁_le
  set r13 := regUpd (regUpd r12 regS6 (r12 regS6 - r12 regEll)) regS1 0
  have h13_S6 : r13 regS6 = paramK n + 1 - paramEll n := by
    dsimp only [r13, r12, r11]
    rw [regUpd_ne _ (by decide), regUpd_self, regUpd_self, regUpd_self,
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h10_K, h10_Ell]
  have e14 := rmSetConst_spec regS7 3 V inp r13 e13.reg₁_le (by omega)
  set r14 := regUpd r13 regS7 3
  rcases rmPow_spec regOmega regS7 regS6 regS1 regS2 regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r14 e14.reg₁_le h1V (by simp [r14, h13_S6]; change paramOmegaExp n ≤ V; omega)
    with ⟨r15, h15_Om, h15_fr, e15⟩
  have h15_Om' : r15 regOmega = paramOmegaExp n := by simpa [r14, h13_S6, paramOmegaExp] using h15_Om
  have h15_keep : ∀ i : Fin EncR,
      i ≠ regL1 → i ≠ regL2 → i ≠ regOmega →
      i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → i ≠ regS5 → i ≠ regS6 → i ≠ regS7 →
      r15 i = reg₀ i := by
    intro i hL1i hL2i hOmi h0 h1 h2 h3 h4 h5 h6 h7
    rw [h15_fr i hOmi h1 h2 h3 h4]
    dsimp only [r14, r13, r12, r11]
    rw [regUpd_ne _ h7, regUpd_ne _ h1, regUpd_ne _ h6, regUpd_ne _ h6, regUpd_ne _ h6]
    exact h10_keep i hL1i hL2i h0 h1 h2 h3 h4 h5 h6 h7
  have h15_J : r15 regJ = paramJ n := by
    rw [h15_keep regJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hJ]
  have h15_L : r15 regL = paramL n := by
    rw [h15_keep regL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hL]
  -- InvOmega = 3 * J - Omega; TwoJ = 2 * J; TwoJL = TwoJ * L
  have e16 := rmSetConst_spec regS0 3 V inp r15 e15.reg₁_le (by omega)
  set r16 := regUpd r15 regS0 3
  rcases rmMul_spec regInvOmega regS0 regJ regS1 regS2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r16 e16.reg₁_le (by simp [r16, h15_J]; omega)
    with ⟨r17, h17_IO, h17_fr, e17⟩
  have h17_IO' : r17 regInvOmega = 3 * paramJ n := by simpa [r16, h15_J] using h17_IO
  have h17_Om : r17 regOmega = paramOmegaExp n := by
    rw [h17_fr regOmega (by decide) (by decide) (by decide)]; simp [r16, h15_Om']
  have e18 := rmSub_spec regInvOmega regOmega regS1 (by decide) V inp r17 e17.reg₁_le
  set r18 := regUpd (regUpd r17 regInvOmega (r17 regInvOmega - r17 regOmega)) regS1 0
  have h18_IO : r18 regInvOmega = paramInvOmegaExp n := by
    dsimp only [r18]; rw [regUpd_ne _ (by decide), regUpd_self, h17_IO', h17_Om]; rfl
  have h18_J : r18 regJ = paramJ n := by
    dsimp only [r18]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h17_fr regJ (by decide) (by decide) (by decide)]; simp [r16, h15_J]
  have h18_L : r18 regL = paramL n := by
    dsimp only [r18]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h17_fr regL (by decide) (by decide) (by decide)]; simp [r16, h15_L]
  have e19 := rmCopy_spec regTwoJ regJ V inp r18 e18.reg₁_le
  set r19 := regUpd r18 regTwoJ (r18 regJ)
  have e20 := rmAdd_spec regTwoJ regJ regS1 (by decide) (by decide) V inp r19 e19.reg₁_le
    (by dsimp only [r19]; rw [regUpd_self, regUpd_ne _ (by decide), h18_J]; omega)
  set r20 := regUpd (regUpd r19 regTwoJ (r19 regTwoJ + r19 regJ)) regS1 0
  have h20_2J : r20 regTwoJ = 2 * paramJ n := by
    dsimp only [r20, r19]; rw [regUpd_ne _ (by decide), regUpd_self, regUpd_self, regUpd_ne _ (by decide), h18_J]; omega
  have h20_L : r20 regL = paramL n := by
    dsimp only [r20, r19]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h18_L]
  rcases rmMul_spec regTwoJL regTwoJ regL regS1 regS2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r20 e20.reg₁_le (by rw [h20_2J, h20_L]; omega)
    with ⟨r21, h21_2JL, h21_fr, e21⟩
  have h21_2JL' : r21 regTwoJL = 2 * paramJ n * paramL n := by rw [h21_2JL, h20_2J, h20_L]
  have h21_keep : ∀ i : Fin EncR,
      i ≠ regL1 → i ≠ regL2 → i ≠ regOmega → i ≠ regInvOmega → i ≠ regTwoJ → i ≠ regTwoJL →
      i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → i ≠ regS5 → i ≠ regS6 → i ≠ regS7 →
      r21 i = reg₀ i := by
    intro i hL1i hL2i hOmi hIOi h2Ji h2JLi h0 h1 h2 h3 h4 h5 h6 h7
    rw [h21_fr i h2JLi h1 h2]
    dsimp only [r20, r19, r18]
    rw [regUpd_ne _ h1, regUpd_ne _ h2Ji, regUpd_ne _ h2Ji, regUpd_ne _ h1, regUpd_ne _ hIOi,
        h17_fr i hIOi h1 h2]
    dsimp only [r16]; rw [regUpd_ne _ h0]
    exact h15_keep i hL1i hL2i hOmi h0 h1 h2 h3 h4 h5 h6 h7
  -- Chain all 21 steps
  have hact_sc : ∀ (r : Fin EncR) (c : ℕ), rmSetConst r c rmSetConstEntry ≠ none := fun _ _ => by
    simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]
  have hact_pow : ∀ (a b c d e f g : Fin EncR), rmPow a b c d e f g rmPowEntry ≠ none := by
    intros; simp [rmPow, rmPowEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hact_add : ∀ (a b c : Fin EncR), rmAdd a b c rmAddEntry ≠ none := by
    intros; simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]
  have hact_sub : ∀ (a b c : Fin EncR), rmSub a b c rmSubEntry ≠ none := by
    intros; simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]
  have hact_mul : ∀ (a b c d e : Fin EncR), rmMul a b c d e rmMulEntry ≠ none := by
    intros; simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]
  have hact_div : ∀ (a b c d e f g : Fin EncR), rmDivMod a b c d e f g rmDivModEntry ≠ none := by
    intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
  have hchain :=
    rmChain_spec_inl (hact_sc _ _) e1 (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) e2
      (rmChain_spec_inl (hact_sc _ _) e3 (rmChain_spec_inl (hact_pow _ _ _ _ _ _ _) e4
        (rmChain_spec_inl (by simp [rmCopy]) e5 (rmChain_spec_inl (by simp [rmInc]) e6
          (rmChain_spec_inl (hact_sc _ _) e7 (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) e8
            (rmChain_spec_inl (hact_sc _ _) e9 (rmChain_spec_inl (hact_pow _ _ _ _ _ _ _) e10
              (rmChain_spec_inl (by simp [rmCopy]) e11 (rmChain_spec_inl (by simp [rmInc]) e12
                (rmChain_spec_inl (hact_sub _ _ _) e13 (rmChain_spec_inl (hact_sc _ _) e14
                  (rmChain_spec_inl (hact_pow _ _ _ _ _ _ _) e15 (rmChain_spec_inl (hact_sc _ _) e16
                    (rmChain_spec_inl (hact_mul _ _ _ _ _) e17 (rmChain_spec_inl (hact_sub _ _ _) e18
                      (rmChain_spec_inl (by simp [rmCopy]) e19 (rmChain_spec_inl (hact_add _ _ _) e20
                        e21)))))))))))))))))))
  have hT_le :
      (1 + 2) + ((15 * r1 regEll + 2 * r1 regS0 + 10) + ((1 + 3) +
        ((r3 regS1 * (V * (2 * r3 regS7 + 3) + 5) + 4) + (1 + (1 + ((1 + 2) +
          ((15 * r7 regS6 + 2 * r7 regS0 + 10) + ((1 + 3) +
            ((r9 regS1 * (V * (2 * r9 regS7 + 3) + 5) + 4) + (1 + (1 + ((2 * r12 regEll + 2) +
              ((1 + 3) + ((r14 regS6 * (V * (2 * r14 regS7 + 3) + 5) + 4) + ((1 + 3) +
                ((r16 regS0 * (2 * r16 regJ + 3) + 3) + ((2 * r17 regOmega + 2) +
                  (1 + ((2 * r19 regJ + 2) + (r20 regTwoJ * (2 * r20 regL + 3) + 3)))))))))))))))))))) ≤
      100 * n * V + 2000 * n ^ 2 + 1000 * n + 200 := by
    have hr1E : r1 regEll = paramEll n := by dsimp only [r1]; rw [regUpd_ne _ (by decide), hEll]
    have hr1S0 : r1 regS0 = 2 := regUpd_self _ _ _
    have hr3S1 : r3 regS1 = paramEll n / 2 := by dsimp only [r3]; rw [regUpd_ne _ (by decide), h2_S1]
    have hr3S7 : r3 regS7 = 3 := regUpd_self _ _ _
    have hr7S0 : r7 regS0 = 2 := regUpd_self _ _ _
    have hr9S1 : r9 regS1 = (paramEll n + 1) / 2 := by dsimp only [r9]; rw [regUpd_ne _ (by decide), h8_S1]
    have hr9S7 : r9 regS7 = 3 := regUpd_self _ _ _
    have hr12E : r12 regEll = paramEll n := by
      dsimp only [r12, r11]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), h10_Ell]
    have hr14S6 : r14 regS6 = paramK n + 1 - paramEll n := by
      dsimp only [r14]; rw [regUpd_ne _ (by decide), h13_S6]
    have hr14S7 : r14 regS7 = 3 := regUpd_self _ _ _
    have hr16S0 : r16 regS0 = 3 := regUpd_self _ _ _
    have hr16J : r16 regJ = paramJ n := by dsimp only [r16]; rw [regUpd_ne _ (by decide), h15_J]
    have hr19J : r19 regJ = paramJ n := by dsimp only [r19]; rw [regUpd_ne _ (by decide), h18_J]
    rw [hr1E, hr1S0, hr3S1, hr3S7, h7_S6, hr7S0, hr9S1, hr9S7, hr12E, hr14S6, hr14S7,
        hr16S0, hr16J, h17_Om, hr19J, h20_2J, h20_L]
    have hp1 : paramEll n / 2 * (V * 9 + 5) ≤ (n + 1) * (V * 9 + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp2 : (paramEll n + 1) / 2 * (V * 9 + 5) ≤ (n + 1) * (V * 9 + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp3 : (paramK n + 1 - paramEll n) * (V * 9 + 5) ≤ (n + 1) * (V * 9 + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp4 : 2 * paramJ n * (2 * paramL n + 3) ≤ (18 * n) * (54 * n + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hlin1 : (n + 1) * (V * 9 + 5) = 9 * (n * V) + 9 * V + 5 * n + 5 := by ring
    have hlin2 : (18 * n) * (54 * n + 3) = 972 * n ^ 2 + 54 * n := by ring
    have hV_le_nV : V ≤ n * V := Nat.le_mul_of_pos_left V hn
    have h100 : 100 * n * V = 100 * (n * V) := by ring
    linarith
  have hfinal := hchain.weaken (V₂ := V) (T₂ := 100 * n * V + 2000 * n ^ 2 + 1000 * n + 200)
    (by simp) hT_le
  simp only [List.nil_append] at hfinal
  have h21_L1 : r21 regL1 = paramL1 n := by
    rw [h21_fr regL1 (by decide) (by decide) (by decide)]
    dsimp only [r20, r19, r18]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h17_fr regL1 (by decide) (by decide) (by decide)]
    dsimp only [r16]; rw [regUpd_ne _ (by decide),
        h15_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r14, r13, r12, r11]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h10_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r9]; rw [regUpd_ne _ (by decide),
        h8_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r7, r6, r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h4_L1']
  have h21_L2 : r21 regL2 = paramL2 n := by
    rw [h21_fr regL2 (by decide) (by decide) (by decide)]
    dsimp only [r20, r19, r18]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h17_fr regL2 (by decide) (by decide) (by decide)]
    dsimp only [r16]; rw [regUpd_ne _ (by decide),
        h15_fr regL2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [r14, r13, r12, r11]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h10_L2']
  have h21_Om : r21 regOmega = paramOmegaExp n := by
    rw [h21_fr regOmega (by decide) (by decide) (by decide)]
    dsimp only [r20, r19, r18]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), h17_Om]
  have h21_IO : r21 regInvOmega = paramInvOmegaExp n := by
    rw [h21_fr regInvOmega (by decide) (by decide) (by decide)]
    dsimp only [r20, r19]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), h18_IO]
  have h21_2J : r21 regTwoJ = 2 * paramJ n := by
    rw [h21_fr regTwoJ (by decide) (by decide) (by decide), h20_2J]
  refine ⟨r21,
    by rw [h21_keep regN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hN],
    by rw [h21_keep regK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hK],
    by rw [h21_keep regJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hJ],
    by rw [h21_keep regM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hM],
    by rw [h21_keep regEll (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hEll],
    by rw [h21_keep regL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL],
    h21_L1, h21_L2, h21_Om, h21_IO, h21_2J, h21_2JL', ?_, hfinal⟩
  intro i hi1 hi2
  exact h21_keep i
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)
    (by intro h; subst h; simp at hi1 hi2) (by intro h; subst h; simp at hi1 hi2)

/-- Phase B: computes `treeLog n` and `treeM n` from `regN = n`. -/
abbrev RMParamsTreeQ : Type :=
  RMSetConstQ 2 ⊕ (RMMinPowExpQ ⊕ (Option Bool ⊕ ((Bool ⊕ RMAddQ) ⊕ (Bool ⊕ Unit))))

def rmParamsTree : RMProg EncR RMParamsTreeQ :=
  rmChain (rmSetConst regS0 2)
    (rmChain (rmMinPowExp regTreeLog regS0 regN regTreeM regS2 regS3 regS4 regS5)
      (rmIfZero regTreeLog
        (rmChain (rmInc regTreeLog) (rmAdd regTreeM regTreeM regS1) rmAddEntry)
        rmNop (Sum.inl false) ())
      rmIfZeroEntry)
    (Sum.inl rmMinPowExpEntry)

def rmParamsTreeEntry : RMParamsTreeQ := Sum.inl rmSetConstEntry

lemma rmParamsTree_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hN : reg₀ regN = n) (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ q₁ reg₁,
      reg₁ regTreeLog = treeLog n ∧
      reg₁ regTreeM = treeM n ∧
      (∀ i, i ≠ regTreeLog → i ≠ regTreeM →
        i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → i ≠ regS5 → reg₁ i = reg₀ i) ∧
      RMExec rmParamsTree V inp rmParamsTreeEntry reg₀ q₁ reg₁ []
        (10 * n ^ 2 + 20 * n + 30) := by
  have h1V : 1 ≤ V := by omega
  have hs1 := rmSetConst_spec regS0 2 V inp reg₀ hreg₀ (by omega)
  set r1 := regUpd reg₀ regS0 2
  rcases rmMinPowExp_spec regTreeLog regS0 regN regTreeM regS2 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r1 (by simp [r1]) hs1.reg₁_le h1V (by simp [r1, hN]; omega)
    with ⟨r2, h2_tl, h2_tm, h2_fr, e2⟩
  have h2_tl' : r2 regTreeLog = minPowExp 2 n := by simpa [r1, hN] using h2_tl
  have h2_tm' : r2 regTreeM = 2 ^ minPowExp 2 n := by simpa [r1, hN] using h2_tm
  have hact_sc : rmSetConst regS0 2 rmSetConstEntry ≠ none := by
    simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]
  have hact_mp : rmMinPowExp regTreeLog regS0 regN regTreeM regS2 regS3 regS4 regS5 rmMinPowExpEntry ≠ none := by
    simp [rmMinPowExp, rmMinPowExpEntry, rmChain, rmSeq, rmZero]
  have hT_mp : r1 regN * (r1 regN * (2 * r1 regS0 + 5) + 15) + 11 = 9 * n ^ 2 + 15 * n + 11 := by
    have : r1 regN = n := by dsimp only [r1]; rw [regUpd_ne _ (by decide), hN]
    have : r1 regS0 = 2 := regUpd_self _ _ _
    rw [‹r1 regN = n›, ‹r1 regS0 = 2›]; ring
  by_cases h0 : minPowExp 2 n = 0
  · have h2_tl0 : r2 regTreeLog = 0 := by rw [h2_tl', h0]
    have h2_tm1 : r2 regTreeM = 1 := by rw [h2_tm', h0]; rfl
    have hinc := rmInc_spec regTreeLog V inp r2 e2.reg₁_le (by rw [h2_tl0]; omega)
    set r3 := regUpd r2 regTreeLog (r2 regTreeLog + 1)
    have h3_tm : r3 regTreeM = 1 := by dsimp only [r3]; rw [regUpd_ne _ (by decide), h2_tm1]
    have hadd := rmAdd_spec regTreeM regTreeM regS1 (by decide) (by decide) V inp r3 hinc.reg₁_le
      (by rw [h3_tm]; omega)
    set r4 := regUpd (regUpd r3 regTreeM (r3 regTreeM + r3 regTreeM)) regS1 0
    have hthen := rmChain_spec_inl (by simp [rmInc]) hinc hadd
    simp only [max_self, List.nil_append] at hthen
    have hif := rmIfZero_zero_spec regTreeLog rmNop () h2_tl0 hthen
    have hcomb := rmChain_spec_inl hact_sc hs1 (rmChain_spec_inl hact_mp e2 hif)
    have hcomb' := hcomb.weaken (V₂ := V) (T₂ := 10 * n ^ 2 + 20 * n + 30) (by simp) (by
      rw [hT_mp, h3_tm]; omega)
    simp only [List.nil_append] at hcomb'
    refine ⟨_, r4, ?_, ?_, ?_, hcomb'⟩
    · dsimp only [r4, r3]
      rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_self, h2_tl0]
      simp [treeLog, h0]
    · dsimp only [r4]
      rw [regUpd_ne _ (by decide), regUpd_self, h3_tm]
      simp [treeM, treeLog, h0]
    · intro i htl htm h0i h1i h2i h3i h4i h5i
      dsimp only [r4, r3]
      rw [regUpd_ne _ h1i, regUpd_ne _ htm, regUpd_ne _ htl,
          h2_fr i htl htm h2i h3i h4i h5i]
      dsimp only [r1]; rw [regUpd_ne _ h0i]
  · have h2_tlne : r2 regTreeLog ≠ 0 := by rw [h2_tl']; exact h0
    have hif := rmIfZero_pos_spec regTreeLog
      (rmChain (rmInc regTreeLog) (rmAdd regTreeM regTreeM regS1) rmAddEntry) (Sum.inl false)
      h2_tlne (rmNop_spec V inp r2 e2.reg₁_le)
    have hcomb := rmChain_spec_inl hact_sc hs1 (rmChain_spec_inl hact_mp e2 hif)
    have hcomb' := hcomb.weaken (V₂ := V) (T₂ := 10 * n ^ 2 + 20 * n + 30) (by simp) (by
      rw [hT_mp]; omega)
    simp only [List.nil_append] at hcomb'
    have htl_eq : treeLog n = minPowExp 2 n := by unfold treeLog; omega
    refine ⟨_, r2, by rw [h2_tl', htl_eq], by rw [h2_tm', treeM, htl_eq], ?_, hcomb'⟩
    intro i htl htm h0i _ h2i h3i h4i h5i
    rw [h2_fr i htl htm h2i h3i h4i h5i]
    dsimp only [r1]; rw [regUpd_ne _ h0i]

/-- Helper macro: sets `dst := a + b` (preserving `a, b`, using `regS0` as scratch). -/
abbrev RMSetAddQ : Type := Bool ⊕ RMAddQ

def rmSetAdd (dst a b : Fin EncR) : RMProg EncR RMSetAddQ :=
  rmChain (rmCopy dst a) (rmAdd dst b regS0) rmAddEntry

def rmSetAddEntry : RMSetAddQ := Sum.inl false
def rmSetAddExit : RMSetAddQ := Sum.inr rmAddExit

lemma rmSetAdd_spec (dst a b : Fin EncR)
    (hd0 : dst ≠ regS0) (hb0 : b ≠ regS0) (hdb : dst ≠ b)
    (V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hreg : ∀ i, reg i ≤ V) (hle : reg a + reg b ≤ V) :
    RMExec (rmSetAdd dst a b) V inp rmSetAddEntry reg rmSetAddExit
      (regUpd (regUpd reg dst (reg a + reg b)) regS0 0) [] (2 * reg b + 3) := by
  have hc := rmCopy_spec dst a V inp reg hreg
  set r1 := regUpd reg dst (reg a)
  have h1_b : r1 b = reg b := regUpd_ne reg hdb.symm _
  have ha := rmAdd_spec dst b regS0 hd0 hb0 V inp r1 hc.reg₁_le
    (by rw [h1_b]; dsimp only [r1]; rw [regUpd_self]; exact hle)
  have hupd : regUpd (regUpd r1 dst (r1 dst + r1 b)) regS0 0 =
      regUpd (regUpd reg dst (reg a + reg b)) regS0 0 := by
    funext i
    by_cases h0 : i = regS0
    · subst h0; simp
    · by_cases hd : i = dst
      · subst hd; simp [regUpd_ne _ h0, r1, h1_b]
      · simp [regUpd, h0, hd, r1]
  rw [hupd] at ha
  have hcomb := rmChain_spec_inl (by simp [rmCopy]) hc ha
  simpa [rmSetAdd, rmSetAddEntry, rmSetAddExit, max_self, h1_b,
    show 1 + (2 * reg b + 2) = 2 * reg b + 3 by omega] using hcomb

/-- Phase C1: computes `V1..V13`. -/
abbrev RMParamsV1to13Q : Type :=
  RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕
    (RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕
      (RMSetAddQ ⊕ (RMSetAddQ ⊕ RMSetAddQ)))))))))))

def rmParamsV1to13 : RMProg EncR RMParamsV1to13Q :=
  rmChain (rmSetAdd regV1 regN regN)
    (rmChain (rmSetAdd regV2 regV1 regV1)
      (rmChain (rmSetAdd regV3 regV2 regN)
        (rmChain (rmSetAdd regV4 regV3 regL2)
          (rmChain (rmSetAdd regV5 regV4 regL1)
            (rmChain (rmSetAdd regV6 regV5 regL2)
              (rmChain (rmSetAdd regV7 regV6 regL1)
                (rmChain (rmSetAdd regV8 regV7 regL)
                  (rmChain (rmSetAdd regV9 regV8 regL2)
                    (rmChain (rmSetAdd regV10 regV9 regL1)
                      (rmChain (rmSetAdd regV11 regV10 regTwoJL)
                        (rmChain (rmSetAdd regV12 regV11 regV1)
                          (rmSetAdd regV13 regV12 regN)
                          rmSetAddEntry)
                        (Sum.inl rmSetAddEntry))
                      (Sum.inl rmSetAddEntry))
                    (Sum.inl rmSetAddEntry))
                  (Sum.inl rmSetAddEntry))
                (Sum.inl rmSetAddEntry))
              (Sum.inl rmSetAddEntry))
            (Sum.inl rmSetAddEntry))
          (Sum.inl rmSetAddEntry))
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmSetAddEntry)

def rmParamsV1to13Entry : RMParamsV1to13Q := Sum.inl rmSetAddEntry
def rmParamsV1to13Exit : RMParamsV1to13Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmSetAddExit)))))))))))

lemma rmParamsV1to13_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n)
    (hN : reg₀ regN = n) (hL : reg₀ regL = paramL n)
    (hL1 : reg₀ regL1 = paramL1 n) (hL2 : reg₀ regL2 = paramL2 n)
    (h2JL : reg₀ regTwoJL = 2 * paramJ n * paramL n)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      reg₁ regV1 = netV1 n ∧ reg₁ regV2 = netV2 n ∧ reg₁ regV3 = netV3 n ∧
      reg₁ regV4 = netV4 n ∧ reg₁ regV5 = netV5 n ∧ reg₁ regV6 = netV6 n ∧
      reg₁ regV7 = netV7 n ∧ reg₁ regV8 = netV8 n ∧ reg₁ regV9 = netV9 n ∧
      reg₁ regV10 = netV10 n ∧ reg₁ regV11 = netV11 n ∧ reg₁ regV12 = netV12 n ∧
      reg₁ regV13 = netV13 n ∧
      (∀ i, (i.val < 14 ∨ 27 ≤ i.val) → i ≠ regS0 → reg₁ i = reg₀ i) ∧
      RMExec rmParamsV1to13 V inp rmParamsV1to13Entry reg₀ rmParamsV1to13Exit reg₁ []
        (500 * n + 60) := by
  have hL_le := paramL_le_27_mul hn
  have hL1_le : paramL1 n ≤ 27 * n := le_trans (paramL1_le_paramL n) hL_le
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) hL_le
  have h2JL_lt := two_J_L_lt hn
  have hvc := netVertCount_le hn
  have hv13_le : netV13 n ≤ 500 * n + 20 := by
    have : netV13 n ≤ netVertCount n := by
      simp only [netVertCount, netV18, netV17, netV16, netV15, netV14]; omega
    omega
  -- Helper shorthand for chaining `rmSetAdd`
  have hact_sa : ∀ d a b, rmSetAdd d a b rmSetAddEntry ≠ none := fun _ _ _ => by
    simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
  -- Step 1..13
  have e1 := rmSetAdd_spec regV1 regN regN (by decide) (by decide) (by decide) V inp reg₀ hreg₀ (by rw [hN]; omega)
  set r1 := regUpd (regUpd reg₀ regV1 (reg₀ regN + reg₀ regN)) regS0 0
  have r1_V1 : r1 regV1 = netV1 n := by simp [r1, hN, netV1]; omega
  have e2 := rmSetAdd_spec regV2 regV1 regV1 (by decide) (by decide) (by decide) V inp r1 e1.reg₁_le (by rw [r1_V1]; simp [netV1]; omega)
  set r2 := regUpd (regUpd r1 regV2 (r1 regV1 + r1 regV1)) regS0 0
  have r2_V2 : r2 regV2 = netV2 n := by simp [r2, r1_V1, netV1, netV2]; omega
  have r2_N : r2 regN = n := by simp [r2, r1, hN]
  have e3 := rmSetAdd_spec regV3 regV2 regN (by decide) (by decide) (by decide) V inp r2 e2.reg₁_le (by rw [r2_V2, r2_N]; simp [netV2]; omega)
  set r3 := regUpd (regUpd r2 regV3 (r2 regV2 + r2 regN)) regS0 0
  have r3_V3 : r3 regV3 = netV3 n := by simp [r3, r2_V2, r2_N, netV2, netV3]; omega
  have r3_L2 : r3 regL2 = paramL2 n := by simp [r3, r2, r1, hL2]
  have e4 := rmSetAdd_spec regV4 regV3 regL2 (by decide) (by decide) (by decide) V inp r3 e3.reg₁_le (by rw [r3_V3, r3_L2]; simp [netV3]; omega)
  set r4 := regUpd (regUpd r3 regV4 (r3 regV3 + r3 regL2)) regS0 0
  have r4_V4 : r4 regV4 = netV4 n := by simp [r4, r3_V3, r3_L2, netV3, netV4]
  have r4_L1 : r4 regL1 = paramL1 n := by simp [r4, r3, r2, r1, hL1]
  have e5 := rmSetAdd_spec regV5 regV4 regL1 (by decide) (by decide) (by decide) V inp r4 e4.reg₁_le (by rw [r4_V4, r4_L1]; simp [netV4]; omega)
  set r5 := regUpd (regUpd r4 regV5 (r4 regV4 + r4 regL1)) regS0 0
  have r5_V5 : r5 regV5 = netV5 n := by simp [r5, r4_V4, r4_L1, netV4, netV5]
  have r5_L2 : r5 regL2 = paramL2 n := by simp [r5, r4, r3_L2]
  have e6 := rmSetAdd_spec regV6 regV5 regL2 (by decide) (by decide) (by decide) V inp r5 e5.reg₁_le (by rw [r5_V5, r5_L2]; simp [netV5]; omega)
  set r6 := regUpd (regUpd r5 regV6 (r5 regV5 + r5 regL2)) regS0 0
  have r6_V6 : r6 regV6 = netV6 n := by simp [r6, r5_V5, r5_L2, netV5, netV6]; omega
  have r6_L1 : r6 regL1 = paramL1 n := by simp [r6, r5, r4_L1]
  have e7 := rmSetAdd_spec regV7 regV6 regL1 (by decide) (by decide) (by decide) V inp r6 e6.reg₁_le (by rw [r6_V6, r6_L1]; simp [netV6]; omega)
  set r7 := regUpd (regUpd r6 regV7 (r6 regV6 + r6 regL1)) regS0 0
  have r7_V7 : r7 regV7 = netV7 n := by simp [r7, r6_V6, r6_L1, netV6, netV7]; omega
  have r7_L : r7 regL = paramL n := by simp [r7, r6, r5, r4, r3, r2, r1, hL]
  have e8 := rmSetAdd_spec regV8 regV7 regL (by decide) (by decide) (by decide) V inp r7 e7.reg₁_le (by rw [r7_V7, r7_L]; simp [netV7]; omega)
  set r8 := regUpd (regUpd r7 regV8 (r7 regV7 + r7 regL)) regS0 0
  have r8_V8 : r8 regV8 = netV8 n := by simp [r8, r7_V7, r7_L, netV8]
  have r8_L2 : r8 regL2 = paramL2 n := by simp [r8, r7, r6, r5_L2]
  have e9 := rmSetAdd_spec regV9 regV8 regL2 (by decide) (by decide) (by decide) V inp r8 e8.reg₁_le (by rw [r8_V8, r8_L2]; simp [netV8, netV7]; omega)
  set r9 := regUpd (regUpd r8 regV9 (r8 regV8 + r8 regL2)) regS0 0
  have r9_V9 : r9 regV9 = netV9 n := by simp [r9, r8_V8, r8_L2, netV9]
  have r9_L1 : r9 regL1 = paramL1 n := by simp [r9, r8, r7, r6_L1]
  have e10 := rmSetAdd_spec regV10 regV9 regL1 (by decide) (by decide) (by decide) V inp r9 e9.reg₁_le (by rw [r9_V9, r9_L1]; simp [netV9, netV8, netV7]; omega)
  set r10 := regUpd (regUpd r9 regV10 (r9 regV9 + r9 regL1)) regS0 0
  have r10_V10 : r10 regV10 = netV10 n := by simp [r10, r9_V9, r9_L1, netV10]
  have r10_2JL : r10 regTwoJL = 2 * paramJ n * paramL n := by
    simp [r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, h2JL]
  have e11 := rmSetAdd_spec regV11 regV10 regTwoJL (by decide) (by decide) (by decide) V inp r10 e10.reg₁_le
    (by rw [r10_V10, r10_2JL]; simp [netV10, netV9, netV8, netV7]; omega)
  set r11 := regUpd (regUpd r10 regV11 (r10 regV10 + r10 regTwoJL)) regS0 0
  have r11_V11 : r11 regV11 = netV11 n := by simp [r11, r10_V10, r10_2JL, netV11]
  have r11_V1 : r11 regV1 = netV1 n := by
    simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1_V1]
  have e12 := rmSetAdd_spec regV12 regV11 regV1 (by decide) (by decide) (by decide) V inp r11 e11.reg₁_le
    (by rw [r11_V11, r11_V1]; simp [netV11, netV10, netV9, netV8, netV7, netV1]; omega)
  set r12 := regUpd (regUpd r11 regV12 (r11 regV11 + r11 regV1)) regS0 0
  have r12_V12 : r12 regV12 = netV12 n := by simp [r12, r11_V11, r11_V1, netV12, netV1]
  have r12_N : r12 regN = n := by
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2_N]
  have e13 := rmSetAdd_spec regV13 regV12 regN (by decide) (by decide) (by decide) V inp r12 e12.reg₁_le
    (by rw [r12_V12, r12_N]; change netV13 n ≤ V; omega)
  set r13 := regUpd (regUpd r12 regV13 (r12 regV12 + r12 regN)) regS0 0
  have hchain :=
    rmChain_spec_inl (hact_sa _ _ _) e1 (rmChain_spec_inl (hact_sa _ _ _) e2
      (rmChain_spec_inl (hact_sa _ _ _) e3 (rmChain_spec_inl (hact_sa _ _ _) e4
        (rmChain_spec_inl (hact_sa _ _ _) e5 (rmChain_spec_inl (hact_sa _ _ _) e6
          (rmChain_spec_inl (hact_sa _ _ _) e7 (rmChain_spec_inl (hact_sa _ _ _) e8
            (rmChain_spec_inl (hact_sa _ _ _) e9 (rmChain_spec_inl (hact_sa _ _ _) e10
              (rmChain_spec_inl (hact_sa _ _ _) e11 (rmChain_spec_inl (hact_sa _ _ _) e12 e13)))))))))))
  have hfinal := hchain.weaken (V₂ := V) (T₂ := 500 * n + 60) (by simp) (by
    rw [hN, r1_V1, r2_N, r3_L2, r4_L1, r5_L2, r6_L1, r7_L, r8_L2, r9_L1, r10_2JL, r11_V1, r12_N]
    simp only [netV1]; omega)
  simp only [List.nil_append] at hfinal
  refine ⟨r13,
    by simp [r13, r12, r11_V1],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2_V2],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3_V3],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4_V4],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6, r5_V5],
    by simp [r13, r12, r11, r10, r9, r8, r7, r6_V6],
    by simp [r13, r12, r11, r10, r9, r8, r7_V7],
    by simp [r13, r12, r11, r10, r9, r8_V8],
    by simp [r13, r12, r11, r10, r9_V9],
    by simp [r13, r12, r11, r10_V10],
    by simp [r13, r12, r11_V11],
    by simp [r13, r12_V12],
    by simp [r13, r12_V12, r12_N, netV13],
    ?_, hfinal⟩
  intro i hi hi0
  have hne : ∀ k : Fin EncR, 14 ≤ k.val → k.val ≤ 26 → i ≠ k := fun k h1 h2 heq => by
    subst heq; omega
  dsimp only [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
  simp only [regUpd_ne _ hi0,
    regUpd_ne _ (hne regV13 (by decide) (by decide)),
    regUpd_ne _ (hne regV12 (by decide) (by decide)),
    regUpd_ne _ (hne regV11 (by decide) (by decide)),
    regUpd_ne _ (hne regV10 (by decide) (by decide)),
    regUpd_ne _ (hne regV9 (by decide) (by decide)),
    regUpd_ne _ (hne regV8 (by decide) (by decide)),
    regUpd_ne _ (hne regV7 (by decide) (by decide)),
    regUpd_ne _ (hne regV6 (by decide) (by decide)),
    regUpd_ne _ (hne regV5 (by decide) (by decide)),
    regUpd_ne _ (hne regV4 (by decide) (by decide)),
    regUpd_ne _ (hne regV3 (by decide) (by decide)),
    regUpd_ne _ (hne regV2 (by decide) (by decide)),
    regUpd_ne _ (hne regV1 (by decide) (by decide))]

/-- Phase C2: computes `V14..V18`, `VertCount`, and `EdgeCount`. -/
abbrev RMParamsV14toEdgeQ : Type :=
  Bool ⊕ (RMSubQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕
    (RMSetConstQ 6 ⊕ (RMMulQ ⊕ (Bool ⊕ (Fin 5 ⊕ (RMSubQ ⊕ (RMSetAddQ ⊕
      (Bool ⊕ (Bool ⊕ (RMSetAddQ ⊕ (Fin 3 ⊕ (Bool ⊕ (Bool ⊕
        (Bool ⊕ (RMSetAddQ ⊕ (RMAddQ ⊕ (RMAddQ ⊕
          (RMSetConstQ 7 ⊕ (RMMulQ ⊕ (RMAddQ ⊕ (RMAddQ ⊕
            (RMSetConstQ 10 ⊕ (RMMulQ ⊕ (RMSetAddQ ⊕ (Fin 8 ⊕
              (RMSubQ ⊕ (RMAddQ ⊕ (RMAddQ ⊕ Fin 4))))))))))))))))))))))))))))))

def rmParamsV14toEdge : RMProg EncR RMParamsV14toEdgeQ :=
  -- V14, V15 using S1 := TreeM - N
  rmChain (rmCopy regS1 regTreeM)
    (rmChain (rmSub regS1 regN regS0)
      (rmChain (rmSetAdd regV14 regV13 regS1)
        (rmChain (rmSetAdd regV15 regV14 regS1)
          -- V16 := V15 + (6 * TreeM - (TreeLog + 4))
          (rmChain (rmSetConst regS1 6)
            (rmChain (rmMul regS2 regS1 regTreeM regS3 regS4)
              (rmChain (rmCopy regS1 regTreeLog)
                (rmChain (rmAddConst regS1 4)
                  (rmChain (rmSub regS2 regS1 regS0)
                    (rmChain (rmSetAdd regV16 regV15 regS2)
                      -- V17 := V16 + 1; V18 := V17 + TreeLog + 2; VertCount := V18 + 1
                      (rmChain (rmCopy regV17 regV16)
                        (rmChain (rmInc regV17)
                          (rmChain (rmSetAdd regV18 regV17 regTreeLog)
                            (rmChain (rmAddConst regV18 2)
                              (rmChain (rmCopy regVertCount regV18)
                                (rmChain (rmInc regVertCount)
                                  -- EdgeCount := V2 + 2*TreeM + N + 7*TwoJL + V1 + (10*TreeM - (2*TreeLog+7)) + TreeLog + 3
                                  (rmChain (rmCopy regEdgeCount regV2)
                                    (rmChain (rmSetAdd regS1 regTreeM regTreeM)
                                      (rmChain (rmAdd regEdgeCount regS1 regS0)
                                        (rmChain (rmAdd regEdgeCount regN regS0)
                                          (rmChain (rmSetConst regS1 7)
                                            (rmChain (rmMul regS2 regS1 regTwoJL regS3 regS4)
                                              (rmChain (rmAdd regEdgeCount regS2 regS0)
                                                (rmChain (rmAdd regEdgeCount regV1 regS0)
                                                  (rmChain (rmSetConst regS1 10)
                                                    (rmChain (rmMul regS2 regS1 regTreeM regS3 regS4)
                                                      (rmChain (rmSetAdd regS1 regTreeLog regTreeLog)
                                                        (rmChain (rmAddConst regS1 7)
                                                          (rmChain (rmSub regS2 regS1 regS0)
                                                            (rmChain (rmAdd regEdgeCount regS2 regS0)
                                                              (rmChain (rmAdd regEdgeCount regTreeLog regS0)
                                                                (rmAddConst regEdgeCount 3)
                                                                ⟨0, by omega⟩)
                                                              (Sum.inl rmAddEntry))
                                                            (Sum.inl rmAddEntry))
                                                          (Sum.inl rmSubEntry))
                                                        (Sum.inl ⟨0, by omega⟩))
                                                      (Sum.inl rmSetAddEntry))
                                                    (Sum.inl rmMulEntry))
                                                  (Sum.inl rmSetConstEntry))
                                                (Sum.inl rmAddEntry))
                                              (Sum.inl rmAddEntry))
                                            (Sum.inl rmMulEntry))
                                          (Sum.inl rmSetConstEntry))
                                        (Sum.inl rmAddEntry))
                                      (Sum.inl rmAddEntry))
                                    (Sum.inl rmSetAddEntry))
                                  (Sum.inl false))
                                (Sum.inl false))
                              (Sum.inl false))
                            (Sum.inl ⟨0, by omega⟩))
                          (Sum.inl rmSetAddEntry))
                        (Sum.inl false))
                      (Sum.inl false))
                    (Sum.inl rmSetAddEntry))
                  (Sum.inl rmSubEntry))
                (Sum.inl ⟨0, by omega⟩))
              (Sum.inl false))
            (Sum.inl rmMulEntry))
          (Sum.inl rmSetConstEntry))
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmSubEntry)

def rmParamsV14toEdgeEntry : RMParamsV14toEdgeQ := Sum.inl false
def rmParamsV14toEdgeExit : RMParamsV14toEdgeQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr ⟨3, by omega⟩))))))))))))))))))))))))))))))

lemma rmParamsV14toEdge_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n)
    (hN : reg₀ regN = n) (hTL : reg₀ regTreeLog = treeLog n) (hTM : reg₀ regTreeM = treeM n)
    (hV1 : reg₀ regV1 = netV1 n) (hV2 : reg₀ regV2 = netV2 n)
    (hV13 : reg₀ regV13 = netV13 n) (h2JL : reg₀ regTwoJL = 2 * paramJ n * paramL n)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      reg₁ regV14 = netV14 n ∧ reg₁ regV15 = netV15 n ∧ reg₁ regV16 = netV16 n ∧
      reg₁ regV17 = netV17 n ∧ reg₁ regV18 = netV18 n ∧
      reg₁ regVertCount = netVertCount n ∧ reg₁ regEdgeCount = netEdgeCount n ∧
      (∀ i, i ≠ regV14 → i ≠ regV15 → i ≠ regV16 → i ≠ regV17 → i ≠ regV18 →
        i ≠ regVertCount → i ≠ regEdgeCount →
        i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → reg₁ i = reg₀ i) ∧
      RMExec rmParamsV14toEdge V inp rmParamsV14toEdgeEntry reg₀ rmParamsV14toEdgeExit reg₁ []
        (2000 * n + 200) := by
  have hM_le := treeM_le_two_mul hn
  have hM_ge := le_treeM n
  have hlog_le := treeLog_le_self hn
  have h2JL_lt := two_J_L_lt hn
  have hvc_le := netVertCount_le hn
  have hec_le := netEdgeCount_le hn
  have hvo := treeVertOff_net n
  have heo := treeEdgeOff_net n
  have hv15_le : netV15 n ≤ netVertCount n := by simp only [netVertCount, netV18, netV17, netV16]; omega
  have hv16_le : netV16 n ≤ netVertCount n := by simp only [netVertCount, netV18, netV17]; omega
  have hv17_le : netV17 n ≤ netVertCount n := by simp only [netVertCount, netV18]; omega
  have hv18_le : netV18 n ≤ netVertCount n := by simp only [netVertCount]; omega
  -- Helper: V14, V15
  have e1 := rmCopy_spec regS1 regTreeM V inp reg₀ hreg₀
  set r1 := regUpd reg₀ regS1 (reg₀ regTreeM)
  have e2 := rmSub_spec regS1 regN regS0 (by decide) V inp r1 e1.reg₁_le
  set r2 := regUpd (regUpd r1 regS1 (r1 regS1 - r1 regN)) regS0 0
  have r2_S1 : r2 regS1 = treeM n - n := by simp [r2, r1, hTM, hN]
  have r2_V13 : r2 regV13 = netV13 n := by simp [r2, r1, hV13]
  have e3 := rmSetAdd_spec regV14 regV13 regS1 (by decide) (by decide) (by decide) V inp r2 e2.reg₁_le
    (by rw [r2_V13, r2_S1]; change netV14 n ≤ V
        have h1415 : netV14 n ≤ netV15 n := by simp [netV15]
        omega)
  set r3 := regUpd (regUpd r2 regV14 (r2 regV13 + r2 regS1)) regS0 0
  have r3_V14 : r3 regV14 = netV14 n := by simp [r3, r2_V13, r2_S1, netV14]
  have r3_S1 : r3 regS1 = treeM n - n := by simp [r3, r2_S1]
  have e4 := rmSetAdd_spec regV15 regV14 regS1 (by decide) (by decide) (by decide) V inp r3 e3.reg₁_le
    (by rw [r3_V14, r3_S1]; change netV15 n ≤ V; omega)
  set r4 := regUpd (regUpd r3 regV15 (r3 regV14 + r3 regS1)) regS0 0
  have r4_V15 : r4 regV15 = netV15 n := by simp [r4, r3_V14, r3_S1, netV15]
  -- V16 := V15 + (6 * treeM - (treeLog + 4))
  have e5 := rmSetConst_spec regS1 6 V inp r4 e4.reg₁_le (by omega)
  set r5 := regUpd r4 regS1 6
  have r5_TM : r5 regTreeM = treeM n := by simp [r5, r4, r3, r2, r1, hTM]
  rcases rmMul_spec regS2 regS1 regTreeM regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r5 e5.reg₁_le (by rw [r5_TM]; simp [r5]; omega)
    with ⟨r6, h6_S2, h6_fr, e6⟩
  have r6_S2 : r6 regS2 = 6 * treeM n := by rw [h6_S2, r5_TM]; simp [r5]
  have r6_TL : r6 regTreeLog = treeLog n := by
    rw [h6_fr regTreeLog (by decide) (by decide) (by decide)]
    simp [r5, r4, r3, r2, r1, hTL]
  have e7 := rmCopy_spec regS1 regTreeLog V inp r6 e6.reg₁_le
  set r7 := regUpd r6 regS1 (r6 regTreeLog)
  have e8 := rmAddConst_spec regS1 4 V inp r7 e7.reg₁_le (by dsimp only [r7]; rw [regUpd_self, r6_TL]; omega)
  set r8 := regUpd r7 regS1 (r7 regS1 + 4)
  have r8_S1 : r8 regS1 = treeLog n + 4 := by dsimp only [r8, r7]; rw [regUpd_self, regUpd_self, r6_TL]
  have r8_S2 : r8 regS2 = 6 * treeM n := by dsimp only [r8, r7]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), r6_S2]
  have e9 := rmSub_spec regS2 regS1 regS0 (by decide) V inp r8 e8.reg₁_le
  set r9 := regUpd (regUpd r8 regS2 (r8 regS2 - r8 regS1)) regS0 0
  have r9_S2 : r9 regS2 = treeVertOff (treeLog n + 1) (treeLog n + 2) := by
    dsimp only [r9]; rw [regUpd_ne _ (by decide), regUpd_self, r8_S2, r8_S1, hvo]
  have r9_V15 : r9 regV15 = netV15 n := by
    dsimp only [r9, r8, r7]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h6_fr regV15 (by decide) (by decide) (by decide)]; simp [r5, r4_V15]
  have e10 := rmSetAdd_spec regV16 regV15 regS2 (by decide) (by decide) (by decide) V inp r9 e9.reg₁_le
    (by rw [r9_V15, r9_S2]; change netV16 n ≤ V; omega)
  set r10 := regUpd (regUpd r9 regV16 (r9 regV15 + r9 regS2)) regS0 0
  have r10_V16 : r10 regV16 = netV16 n := by simp [r10, r9_V15, r9_S2, netV16]
  -- V17, V18, VertCount
  have e11 := rmCopy_spec regV17 regV16 V inp r10 e10.reg₁_le
  set r11 := regUpd r10 regV17 (r10 regV16)
  have e12 := rmInc_spec regV17 V inp r11 e11.reg₁_le (by dsimp only [r11]; rw [regUpd_self, r10_V16]; change netV17 n ≤ V; omega)
  set r12 := regUpd r11 regV17 (r11 regV17 + 1)
  have r12_V17 : r12 regV17 = netV17 n := by dsimp only [r12, r11]; rw [regUpd_self, regUpd_self, r10_V16]; rfl
  have r12_TL : r12 regTreeLog = treeLog n := by
    dsimp only [r12, r11, r10, r9, r8, r7]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), r6_TL]
  have e13 := rmSetAdd_spec regV18 regV17 regTreeLog (by decide) (by decide) (by decide) V inp r12 e12.reg₁_le
    (by rw [r12_V17, r12_TL]
        have h1718 : netV17 n + treeLog n ≤ netV18 n := by simp [netV18]
        omega)
  set r13 := regUpd (regUpd r12 regV18 (r12 regV17 + r12 regTreeLog)) regS0 0
  have e14 := rmAddConst_spec regV18 2 V inp r13 e13.reg₁_le
    (by dsimp only [r13]; rw [regUpd_ne _ (by decide), regUpd_self, r12_V17, r12_TL]
        have h18eq : netV17 n + treeLog n + 2 = netV18 n := by simp [netV18]; omega
        omega)
  set r14 := regUpd r13 regV18 (r13 regV18 + 2)
  have r14_V18 : r14 regV18 = netV18 n := by
    dsimp only [r14, r13]; rw [regUpd_self, regUpd_ne _ (by decide), regUpd_self, r12_V17, r12_TL]; simp [netV18]; omega
  have e15 := rmCopy_spec regVertCount regV18 V inp r14 e14.reg₁_le
  set r15 := regUpd r14 regVertCount (r14 regV18)
  have e16 := rmInc_spec regVertCount V inp r15 e15.reg₁_le
    (by dsimp only [r15]; rw [regUpd_self, r14_V18]; change netVertCount n ≤ V; omega)
  set r16 := regUpd r15 regVertCount (r15 regVertCount + 1)
  have r16_VC : r16 regVertCount = netVertCount n := by
    dsimp only [r16, r15]; rw [regUpd_self, regUpd_self, r14_V18]; rfl
  -- Frame lemma for r16
  have r16_keep : ∀ i : Fin EncR,
      i ≠ regV14 → i ≠ regV15 → i ≠ regV16 → i ≠ regV17 → i ≠ regV18 → i ≠ regVertCount →
      i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 → r16 i = reg₀ i := by
    intro i h14 h15 h16 h17 h18 hvc h0 h1 h2 h3 h4
    dsimp only [r16, r15, r14, r13, r12, r11, r10, r9, r8, r7]
    simp only [regUpd_ne _ hvc, regUpd_ne _ h18, regUpd_ne _ h0, regUpd_ne _ h17,
      regUpd_ne _ h16, regUpd_ne _ h2, regUpd_ne _ h1]
    rw [h6_fr i h2 h3 h4]
    dsimp only [r5, r4, r3, r2, r1]
    simp only [regUpd_ne _ h1, regUpd_ne _ h0, regUpd_ne _ h15, regUpd_ne _ h14]
  -- EdgeCount
  have r16_V2 : r16 regV2 = netV2 n := by
    rw [r16_keep regV2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hV2]
  have r16_TM : r16 regTreeM = treeM n := by
    rw [r16_keep regTreeM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hTM]
  have r16_N : r16 regN = n := by
    rw [r16_keep regN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hN]
  have r16_2JL : r16 regTwoJL = 2 * paramJ n * paramL n := by
    rw [r16_keep regTwoJL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h2JL]
  have r16_V1 : r16 regV1 = netV1 n := by
    rw [r16_keep regV1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hV1]
  have r16_TL : r16 regTreeLog = treeLog n := by
    rw [r16_keep regTreeLog (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hTL]
  have e17 := rmCopy_spec regEdgeCount regV2 V inp r16 e16.reg₁_le
  set r17 := regUpd r16 regEdgeCount (r16 regV2)
  have e18 := rmSetAdd_spec regS1 regTreeM regTreeM (by decide) (by decide) (by decide) V inp r17 e17.reg₁_le
    (by dsimp only [r17]; rw [regUpd_ne _ (by decide), r16_TM]; omega)
  set r18 := regUpd (regUpd r17 regS1 (r17 regTreeM + r17 regTreeM)) regS0 0
  have r18_EC : r18 regEdgeCount = 4 * n := by
    dsimp only [r18, r17]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_self, r16_V2]; rfl
  have r18_S1 : r18 regS1 = 2 * treeM n := by
    dsimp only [r18, r17]; rw [regUpd_ne _ (by decide), regUpd_self, regUpd_ne _ (by decide), r16_TM]; omega
  have e19 := rmAdd_spec regEdgeCount regS1 regS0 (by decide) (by decide) V inp r18 e18.reg₁_le
    (by rw [r18_EC, r18_S1]; omega)
  set r19 := regUpd (regUpd r18 regEdgeCount (r18 regEdgeCount + r18 regS1)) regS0 0
  have r19_EC : r19 regEdgeCount = netE3 n := by
    dsimp only [r19]; rw [regUpd_ne _ (by decide), regUpd_self, r18_EC, r18_S1]; rfl
  have r19_N : r19 regN = n := by
    dsimp only [r19, r18, r17]
    simp only [regUpd_ne _ (by decide : regN ≠ regS0), regUpd_ne _ (by decide : regN ≠ regEdgeCount),
      regUpd_ne _ (by decide : regN ≠ regS1), r16_N]
  have e20 := rmAdd_spec regEdgeCount regN regS0 (by decide) (by decide) V inp r19 e19.reg₁_le
    (by rw [r19_EC, r19_N]; simp [netE3]; omega)
  set r20 := regUpd (regUpd r19 regEdgeCount (r19 regEdgeCount + r19 regN)) regS0 0
  have r20_EC : r20 regEdgeCount = netE4 n := by
    dsimp only [r20]; rw [regUpd_ne _ (by decide), regUpd_self, r19_EC, r19_N]; rfl
  have e21 := rmSetConst_spec regS1 7 V inp r20 e20.reg₁_le (by omega)
  set r21 := regUpd r20 regS1 7
  have r21_2JL : r21 regTwoJL = 2 * paramJ n * paramL n := by
    dsimp only [r21, r20, r19, r18, r17]
    simp only [regUpd_ne _ (by decide : regTwoJL ≠ regS1), regUpd_ne _ (by decide : regTwoJL ≠ regS0),
      regUpd_ne _ (by decide : regTwoJL ≠ regEdgeCount), r16_2JL]
  rcases rmMul_spec regS2 regS1 regTwoJL regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r21 e21.reg₁_le (by rw [r21_2JL]; simp [r21]; omega)
    with ⟨r22, h22_S2, h22_fr, e22⟩
  have r22_S2 : r22 regS2 = 7 * (2 * paramJ n * paramL n) := by rw [h22_S2, r21_2JL]; simp [r21]
  have r22_EC : r22 regEdgeCount = netE4 n := by
    rw [h22_fr regEdgeCount (by decide) (by decide) (by decide)]; simp [r21, r20_EC]
  have e23 := rmAdd_spec regEdgeCount regS2 regS0 (by decide) (by decide) V inp r22 e22.reg₁_le
    (by rw [r22_EC, r22_S2]; simp [netE4, netE3]; omega)
  set r23 := regUpd (regUpd r22 regEdgeCount (r22 regEdgeCount + r22 regS2)) regS0 0
  have r23_EC : r23 regEdgeCount = netE11 n := by
    dsimp only [r23]; rw [regUpd_ne _ (by decide), regUpd_self, r22_EC, r22_S2]
    simp only [netE11, netE10, netE9, netE8, netE7, netE6, netE5]; ring
  have r23_V1 : r23 regV1 = netV1 n := by
    dsimp only [r23]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h22_fr regV1 (by decide) (by decide) (by decide)]
    dsimp only [r21, r20, r19, r18, r17]
    simp only [regUpd_ne _ (by decide : regV1 ≠ regS1), regUpd_ne _ (by decide : regV1 ≠ regS0),
      regUpd_ne _ (by decide : regV1 ≠ regEdgeCount), r16_V1]
  have e24 := rmAdd_spec regEdgeCount regV1 regS0 (by decide) (by decide) V inp r23 e23.reg₁_le
    (by rw [r23_EC, r23_V1]; change netE12 n ≤ V
        have h12ec : netE12 n ≤ netEdgeCount n := by simp only [netEdgeCount, netE13]; omega
        omega)
  set r24 := regUpd (regUpd r23 regEdgeCount (r23 regEdgeCount + r23 regV1)) regS0 0
  have r24_EC : r24 regEdgeCount = netE12 n := by
    dsimp only [r24]; rw [regUpd_ne _ (by decide), regUpd_self, r23_EC, r23_V1]; rfl
  have e25 := rmSetConst_spec regS1 10 V inp r24 e24.reg₁_le (by omega)
  set r25 := regUpd r24 regS1 10
  have r25_TM : r25 regTreeM = treeM n := by
    dsimp only [r25, r24, r23]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h22_fr regTreeM (by decide) (by decide) (by decide)]
    dsimp only [r21, r20, r19, r18, r17]
    simp only [regUpd_ne _ (by decide : regTreeM ≠ regS1), regUpd_ne _ (by decide : regTreeM ≠ regS0),
      regUpd_ne _ (by decide : regTreeM ≠ regEdgeCount), r16_TM]
  rcases rmMul_spec regS2 regS1 regTreeM regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r25 e25.reg₁_le (by rw [r25_TM]; simp [r25]; omega)
    with ⟨r26, h26_S2, h26_fr, e26⟩
  have r26_S2 : r26 regS2 = 10 * treeM n := by rw [h26_S2, r25_TM]; simp [r25]
  have r26_TL : r26 regTreeLog = treeLog n := by
    rw [h26_fr regTreeLog (by decide) (by decide) (by decide)]
    dsimp only [r25, r24, r23]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h22_fr regTreeLog (by decide) (by decide) (by decide)]
    dsimp only [r21, r20, r19, r18, r17]
    simp only [regUpd_ne _ (by decide : regTreeLog ≠ regS1), regUpd_ne _ (by decide : regTreeLog ≠ regS0),
      regUpd_ne _ (by decide : regTreeLog ≠ regEdgeCount), r16_TL]
  have e27 := rmSetAdd_spec regS1 regTreeLog regTreeLog (by decide) (by decide) (by decide) V inp r26 e26.reg₁_le
    (by rw [r26_TL]; omega)
  set r27 := regUpd (regUpd r26 regS1 (r26 regTreeLog + r26 regTreeLog)) regS0 0
  have e28 := rmAddConst_spec regS1 7 V inp r27 e27.reg₁_le
    (by dsimp only [r27]; rw [regUpd_ne _ (by decide), regUpd_self, r26_TL]; omega)
  set r28 := regUpd r27 regS1 (r27 regS1 + 7)
  have r28_S1 : r28 regS1 = 2 * treeLog n + 7 := by
    dsimp only [r28, r27]; rw [regUpd_self, regUpd_ne _ (by decide), regUpd_self, r26_TL]; omega
  have r28_S2 : r28 regS2 = 10 * treeM n := by
    dsimp only [r28, r27]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), r26_S2]
  have e29 := rmSub_spec regS2 regS1 regS0 (by decide) V inp r28 e28.reg₁_le
  set r29 := regUpd (regUpd r28 regS2 (r28 regS2 - r28 regS1)) regS0 0
  have r29_S2 : r29 regS2 = treeEdgeOff (treeLog n + 1) (treeLog n + 2) := by
    dsimp only [r29]; rw [regUpd_ne _ (by decide), regUpd_self, r28_S2, r28_S1, heo]
  have r29_EC : r29 regEdgeCount = netE12 n := by
    dsimp only [r29, r28, r27]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h26_fr regEdgeCount (by decide) (by decide) (by decide)]; simp [r25, r24_EC]
  have e30 := rmAdd_spec regEdgeCount regS2 regS0 (by decide) (by decide) V inp r29 e29.reg₁_le
    (by rw [r29_EC, r29_S2]; change netE13 n ≤ V
        have h13ec : netE13 n ≤ netEdgeCount n := by simp [netEdgeCount]
        omega)
  set r30 := regUpd (regUpd r29 regEdgeCount (r29 regEdgeCount + r29 regS2)) regS0 0
  have r30_EC : r30 regEdgeCount = netE13 n := by
    dsimp only [r30]; rw [regUpd_ne _ (by decide), regUpd_self, r29_EC, r29_S2]; rfl
  have r30_TL : r30 regTreeLog = treeLog n := by
    dsimp only [r30, r29, r28, r27]
    simp only [regUpd_ne _ (by decide : regTreeLog ≠ regS0), regUpd_ne _ (by decide : regTreeLog ≠ regEdgeCount),
      regUpd_ne _ (by decide : regTreeLog ≠ regS2), regUpd_ne _ (by decide : regTreeLog ≠ regS1), r26_TL]
  have e31 := rmAdd_spec regEdgeCount regTreeLog regS0 (by decide) (by decide) V inp r30 e30.reg₁_le
    (by rw [r30_EC, r30_TL]
        have h13l : netE13 n + treeLog n ≤ netEdgeCount n := by simp [netEdgeCount]
        omega)
  set r31 := regUpd (regUpd r30 regEdgeCount (r30 regEdgeCount + r30 regTreeLog)) regS0 0
  have e32 := rmAddConst_spec regEdgeCount 3 V inp r31 e31.reg₁_le
    (by dsimp only [r31]; rw [regUpd_ne _ (by decide), regUpd_self, r30_EC, r30_TL]
        have : netE13 n + treeLog n + 3 = netEdgeCount n := by simp [netEdgeCount]; omega
        omega)
  set r32 := regUpd r31 regEdgeCount (r31 regEdgeCount + 3)
  -- Frame from r16 to r32
  have r32_from_16 : ∀ i : Fin EncR,
      i ≠ regEdgeCount → i ≠ regS0 → i ≠ regS1 → i ≠ regS2 → i ≠ regS3 → i ≠ regS4 →
      r32 i = r16 i := by
    intro i hec h0 h1 h2 h3 h4
    dsimp only [r32, r31, r30, r29, r28, r27]
    simp only [regUpd_ne _ hec, regUpd_ne _ h0, regUpd_ne _ h2, regUpd_ne _ h1]
    rw [h26_fr i h2 h3 h4]
    dsimp only [r25, r24, r23]
    simp only [regUpd_ne _ h1, regUpd_ne _ h0, regUpd_ne _ hec]
    rw [h22_fr i h2 h3 h4]
    dsimp only [r21, r20, r19, r18, r17]
    simp only [regUpd_ne _ h1, regUpd_ne _ h0, regUpd_ne _ hec]
  -- Chain all 32 steps
  have hact_sa : ∀ d a b, rmSetAdd d a b rmSetAddEntry ≠ none := fun _ _ _ => by
    simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
  have hact_sc : ∀ (r : Fin EncR) (c : ℕ), rmSetConst r c rmSetConstEntry ≠ none := fun _ _ => by
    simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]
  have hact_add : ∀ (a b c : Fin EncR), rmAdd a b c rmAddEntry ≠ none := by
    intros; simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]
  have hact_sub : ∀ (a b c : Fin EncR), rmSub a b c rmSubEntry ≠ none := by
    intros; simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]
  have hact_mul : ∀ (a b c d e : Fin EncR), rmMul a b c d e rmMulEntry ≠ none := by
    intros; simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]
  have hact_ac : ∀ (r : Fin EncR) (c : ℕ), 0 < c → rmAddConst r c ⟨0, by omega⟩ ≠ none := fun r c hc => by
    simp [rmAddConst, hc]
  have hchain :=
    rmChain_spec_inl (by simp [rmCopy]) e1 (rmChain_spec_inl (hact_sub _ _ _) e2
      (rmChain_spec_inl (hact_sa _ _ _) e3 (rmChain_spec_inl (hact_sa _ _ _) e4
        (rmChain_spec_inl (hact_sc _ _) e5 (rmChain_spec_inl (hact_mul _ _ _ _ _) e6
          (rmChain_spec_inl (by simp [rmCopy]) e7 (rmChain_spec_inl (hact_ac _ 4 (by decide)) e8
            (rmChain_spec_inl (hact_sub _ _ _) e9 (rmChain_spec_inl (hact_sa _ _ _) e10
              (rmChain_spec_inl (by simp [rmCopy]) e11 (rmChain_spec_inl (by simp [rmInc]) e12
                (rmChain_spec_inl (hact_sa _ _ _) e13 (rmChain_spec_inl (hact_ac _ 2 (by decide)) e14
                  (rmChain_spec_inl (by simp [rmCopy]) e15 (rmChain_spec_inl (by simp [rmInc]) e16
                    (rmChain_spec_inl (by simp [rmCopy]) e17 (rmChain_spec_inl (hact_sa _ _ _) e18
                      (rmChain_spec_inl (hact_add _ _ _) e19 (rmChain_spec_inl (hact_add _ _ _) e20
                        (rmChain_spec_inl (hact_sc _ _) e21 (rmChain_spec_inl (hact_mul _ _ _ _ _) e22
                          (rmChain_spec_inl (hact_add _ _ _) e23 (rmChain_spec_inl (hact_add _ _ _) e24
                            (rmChain_spec_inl (hact_sc _ _) e25 (rmChain_spec_inl (hact_mul _ _ _ _ _) e26
                              (rmChain_spec_inl (hact_sa _ _ _) e27 (rmChain_spec_inl (hact_ac _ 7 (by decide)) e28
                                (rmChain_spec_inl (hact_sub _ _ _) e29 (rmChain_spec_inl (hact_add _ _ _) e30
                                  (rmChain_spec_inl (hact_add _ _ _) e31 e32))))))))))))))))))))))))))))))
  have hfinal := hchain.weaken (V₂ := V) (T₂ := 2000 * n + 200) (by simp) (by
    have hr1N : r1 regN = n := by dsimp only [r1]; rw [regUpd_ne _ (by decide), hN]
    have hr5S1 : r5 regS1 = 6 := regUpd_self _ _ _
    have hr17TM : r17 regTreeM = treeM n := by dsimp only [r17]; rw [regUpd_ne _ (by decide), r16_TM]
    have hr21S1 : r21 regS1 = 7 := regUpd_self _ _ _
    have hr25S1 : r25 regS1 = 10 := regUpd_self _ _ _
    rw [hr1N, r2_S1, r3_S1, hr5S1, r5_TM, r8_S1, r9_S2, r12_TL, hr17TM, r18_S1, r19_N,
        hr21S1, r21_2JL, r22_S2, r23_V1, hr25S1, r25_TM, r26_TL, r28_S1, r29_S2, r30_TL]
    simp only [hvo, heo, netV1]
    have h1 : 6 * treeM n - (treeLog n + 4) ≤ 6 * treeM n := Nat.sub_le _ _
    have h2 : 10 * treeM n - (2 * treeLog n + 7) ≤ 10 * treeM n := Nat.sub_le _ _
    have h3 : treeM n - n ≤ treeM n := Nat.sub_le _ _
    linarith)
  simp only [List.nil_append] at hfinal
  refine ⟨r32,
    by rw [r32_from_16 regV14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       dsimp only [r16, r15, r14, r13, r12, r11, r10, r9, r8, r7]
       simp only [regUpd_ne _ (by decide : regV14 ≠ regVertCount), regUpd_ne _ (by decide : regV14 ≠ regV18),
         regUpd_ne _ (by decide : regV14 ≠ regS0), regUpd_ne _ (by decide : regV14 ≠ regV17),
         regUpd_ne _ (by decide : regV14 ≠ regV16), regUpd_ne _ (by decide : regV14 ≠ regS2),
         regUpd_ne _ (by decide : regV14 ≠ regS1)]
       rw [h6_fr regV14 (by decide) (by decide) (by decide)]
       simp [r5, r4, r3_V14],
    by rw [r32_from_16 regV15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       dsimp only [r16, r15, r14, r13, r12, r11, r10]
       simp only [regUpd_ne _ (by decide : regV15 ≠ regVertCount), regUpd_ne _ (by decide : regV15 ≠ regV18),
         regUpd_ne _ (by decide : regV15 ≠ regS0), regUpd_ne _ (by decide : regV15 ≠ regV17),
         regUpd_ne _ (by decide : regV15 ≠ regV16), r9_V15],
    by rw [r32_from_16 regV16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       dsimp only [r16, r15, r14, r13, r12, r11]
       simp only [regUpd_ne _ (by decide : regV16 ≠ regVertCount), regUpd_ne _ (by decide : regV16 ≠ regV18),
         regUpd_ne _ (by decide : regV16 ≠ regS0), regUpd_ne _ (by decide : regV16 ≠ regV17), r10_V16],
    by rw [r32_from_16 regV17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       dsimp only [r16, r15, r14, r13]
       simp only [regUpd_ne _ (by decide : regV17 ≠ regVertCount), regUpd_ne _ (by decide : regV17 ≠ regV18),
         regUpd_ne _ (by decide : regV17 ≠ regS0), r12_V17],
    by rw [r32_from_16 regV18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
       dsimp only [r16, r15]
       simp only [regUpd_ne _ (by decide : regV18 ≠ regVertCount), r14_V18],
    by rw [r32_from_16 regVertCount (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r16_VC],
    by dsimp only [r32, r31]; rw [regUpd_self, regUpd_ne _ (by decide), regUpd_self, r30_EC, r30_TL]; simp [netEdgeCount]; omega,
    ?_, hfinal⟩
  intro i h14 h15 h16 h17 h18 hvc hec h0 h1 h2 h3 h4
  rw [r32_from_16 i hec h0 h1 h2 h3 h4]
  exact r16_keep i h14 h15 h16 h17 h18 hvc h0 h1 h2 h3 h4

/-- Full parameter-computation macro: from `regN = n ≥ 1`, loads all 34 parameter & offset registers
(`ParamsLoaded n`) while preserving input parser registers `regCur..regOffPre` (`34..40`). -/
abbrev RMComputeParamsQ : Type :=
  RMParamsA1Q ⊕ (RMParamsA2Q ⊕ (RMParamsTreeQ ⊕ (RMParamsV1to13Q ⊕ RMParamsV14toEdgeQ)))

def rmComputeParams : RMProg EncR RMComputeParamsQ :=
  rmChain rmParamsA1
    (rmChain rmParamsA2
      (rmChain rmParamsTree
        (rmChain rmParamsV1to13 rmParamsV14toEdge rmParamsV14toEdgeEntry)
        (Sum.inl rmParamsV1to13Entry))
      (Sum.inl rmParamsTreeEntry))
    (Sum.inl rmParamsA2Entry)

def rmComputeParamsEntry : RMComputeParamsQ := Sum.inl rmParamsA1Entry
def rmComputeParamsExit : RMComputeParamsQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr rmParamsV14toEdgeExit)))

/-- Main Section 3a theorem: `rmComputeParams` computes `paramK`, `paramJ`, `paramM`, `paramEll`,
`paramL`, `paramL1`, `paramL2`, `paramOmegaExp`, `paramInvOmegaExp`, `treeLog`, `treeM`,
`netV1..netV18`, `netVertCount`, and `netEdgeCount` in `O(n^2)` RM steps with `Vmax = V` (for `V ≥ 500n + 20`,
e.g. `V = 500n + 20` gives `O(n^2)` steps and `O(n)` register bound). -/
theorem rmComputeParams_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hN : reg₀ regN = n) (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      ParamsLoaded n reg₁ ∧
      (∀ i, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec rmComputeParams V inp rmComputeParamsEntry reg₀ rmComputeParamsExit reg₁ []
        (200 * n * V + 2210 * n ^ 2 + 4020 * n + 690) := by
  rcases rmParamsA1_spec n V inp reg₀ hn hN hreg₀ hV
    with ⟨r1, h1N, h1K, h1J, h1M, h1Ell, h1L, h1p, e1⟩
  rcases rmParamsA2_spec n V inp r1 hn h1N h1K h1J h1M h1Ell h1L e1.reg₁_le hV
    with ⟨r2, h2N, h2K, h2J, h2M, h2Ell, h2L, h2L1, h2L2, h2Om, h2IO, h22J, h22JL, h2p, e2⟩
  rcases rmParamsTree_spec n V inp r2 hn h2N e2.reg₁_le hV
    with ⟨q3, r3, h3TL, h3TM, h3fr, e3⟩
  have h3_keep : ∀ i : Fin EncR, i ≠ regTreeLog → i ≠ regTreeM → i.val < 41 → r3 i = r2 i := fun i htl htm hi =>
    h3fr i htl htm
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
  rcases rmParamsV1to13_spec n V inp r3 hn
      (by rw [h3_keep regN (by decide) (by decide) (by decide), h2N])
      (by rw [h3_keep regL (by decide) (by decide) (by decide), h2L])
      (by rw [h3_keep regL1 (by decide) (by decide) (by decide), h2L1])
      (by rw [h3_keep regL2 (by decide) (by decide) (by decide), h2L2])
      (by rw [h3_keep regTwoJL (by decide) (by decide) (by decide), h22JL])
      e3.reg₁_le hV
    with ⟨r4, h4V1, h4V2, h4V3, h4V4, h4V5, h4V6, h4V7, h4V8, h4V9, h4V10, h4V11, h4V12, h4V13, h4fr, e4⟩
  rcases rmParamsV14toEdge_spec n V inp r4 hn
      (by rw [h4fr regN (by decide) (by decide), h3_keep regN (by decide) (by decide) (by decide), h2N])
      (by rw [h4fr regTreeLog (by decide) (by decide), h3TL])
      (by rw [h4fr regTreeM (by decide) (by decide), h3TM])
      h4V1 h4V2 h4V13
      (by rw [h4fr regTwoJL (by decide) (by decide), h3_keep regTwoJL (by decide) (by decide) (by decide), h22JL])
      e4.reg₁_le hV
    with ⟨r5, h5V14, h5V15, h5V16, h5V17, h5V18, h5VC, h5EC, h5fr, e5⟩
  have hact1 : rmParamsA1 rmParamsA1Entry ≠ none := by
    simp [rmParamsA1, rmParamsA1Entry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hact2 : rmParamsA2 rmParamsA2Entry ≠ none := by
    simp [rmParamsA2, rmParamsA2Entry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hact3 : rmParamsTree rmParamsTreeEntry ≠ none := by
    simp [rmParamsTree, rmParamsTreeEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hact4 : rmParamsV1to13 rmParamsV1to13Entry ≠ none := by
    simp [rmParamsV1to13, rmParamsV1to13Entry, rmChain, rmSeq, rmSetAdd, rmSetAddEntry, rmCopy]
  have hcomb := rmChain_spec_inl hact1 e1
    (rmChain_spec_inl hact2 e2
      (rmChain_spec_inl hact3 e3
        (rmChain_spec_inl hact4 e4 e5)))
  have hfinal := hcomb.weaken (V₂ := V) (T₂ := 200 * n * V + 2210 * n ^ 2 + 4020 * n + 690)
    (by simp) (by
      have hT : (100 * n * V + 200 * n ^ 2 + 500 * n + 200) +
          ((100 * n * V + 2000 * n ^ 2 + 1000 * n + 200) +
          ((10 * n ^ 2 + 20 * n + 30) + ((500 * n + 60) + (2000 * n + 200)))) =
          200 * n * V + 2210 * n ^ 2 + 4020 * n + 690 := by ring
      omega)
  simp only [List.nil_append] at hfinal
  have h5_r4 : ∀ i : Fin EncR, (i.val < 12 ∨ (14 ≤ i.val ∧ i.val ≤ 26) ∨ (32 ≤ i.val ∧ i.val ≤ 40)) →
      r5 i = r4 i := fun i hi =>
    h5fr i
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
      (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi)
  have h5_r2 : ∀ i : Fin EncR, (i.val < 10 ∨ (32 ≤ i.val ∧ i.val ≤ 40)) → r5 i = r2 i := fun i hi => by
    rw [h5_r4 i (by omega), h4fr i (by omega) (by intro h; subst h; simp at hi),
        h3_keep i (by intro h; subst h; simp at hi) (by intro h; subst h; simp at hi) (by omega)]
  refine ⟨r5, ?_, ?_, hfinal⟩
  · refine ⟨by rw [h5_r2 regN (by decide), h2N],
      by rw [h5_r2 regK (by decide), h2K],
      by rw [h5_r2 regJ (by decide), h2J],
      by rw [h5_r2 regM (by decide), h2M],
      by rw [h5_r2 regEll (by decide), h2Ell],
      by rw [h5_r2 regL (by decide), h2L],
      by rw [h5_r2 regL1 (by decide), h2L1],
      by rw [h5_r2 regL2 (by decide), h2L2],
      by rw [h5_r2 regOmega (by decide), h2Om],
      by rw [h5_r2 regInvOmega (by decide), h2IO],
      by rw [h5_r4 regTreeLog (by decide), h4fr regTreeLog (by decide) (by decide), h3TL],
      by rw [h5_r4 regTreeM (by decide), h4fr regTreeM (by decide) (by decide), h3TM],
      h5VC, h5EC,
      by rw [h5_r4 regV1 (by decide), h4V1], by rw [h5_r4 regV2 (by decide), h4V2],
      by rw [h5_r4 regV3 (by decide), h4V3], by rw [h5_r4 regV4 (by decide), h4V4],
      by rw [h5_r4 regV5 (by decide), h4V5], by rw [h5_r4 regV6 (by decide), h4V6],
      by rw [h5_r4 regV7 (by decide), h4V7], by rw [h5_r4 regV8 (by decide), h4V8],
      by rw [h5_r4 regV9 (by decide), h4V9], by rw [h5_r4 regV10 (by decide), h4V10],
      by rw [h5_r4 regV11 (by decide), h4V11], by rw [h5_r4 regV12 (by decide), h4V12],
      by rw [h5_r4 regV13 (by decide), h4V13],
      h5V14, h5V15, h5V16, h5V17, h5V18,
      by rw [h5_r2 regTwoJ (by decide), h22J],
      by rw [h5_r2 regTwoJL (by decide), h22JL]⟩
  · intro i hi1 hi2
    rw [h5_r2 i (by omega), h2p i hi1 hi2, h1p i hi1 hi2]

/-!
## Section 3b: `rawEnds` Edge-List Emitter (`rmEmitAllEdges`)

Emits `(List.range (netEdgeCount n)).flatMap (fun e => QCSD_natToUnary (rawEnds n e).1 ++ QCSD_natToUnary (rawEnds n e).2)`
in `O(n^3)` RM steps (independent of `V ≥ 500 * n + 20`) while preserving `ParamsLoaded n` and
all input parser registers (`regCur..regOffPre`).
-/

/-- Emitted bit-string for a single directed edge `(u, v)`. -/
def emitEdgeBits (p : ℕ × ℕ) : List Bool :=
  QCSD_natToUnary p.1 ++ QCSD_natToUnary p.2

/-- Preservation of all 34 parameter registers (`0..33`) and all 7 input parser registers (`34..40`). -/
def PreservedRegs (reg₁ reg₀ : RegState EncR) : Prop :=
  ∀ i : Fin EncR, i.val < 41 → reg₁ i = reg₀ i

lemma PreservedRegs.refl (reg : RegState EncR) : PreservedRegs reg reg :=
  fun _ _ => rfl

lemma PreservedRegs.trans {r2 r1 r0 : RegState EncR}
    (h21 : PreservedRegs r2 r1) (h10 : PreservedRegs r1 r0) : PreservedRegs r2 r0 :=
  fun i hi => (h21 i hi).trans (h10 i hi)

lemma PreservedRegs.upd_ge (reg : RegState EncR) (r : Fin EncR) (v : ℕ) (hr : 41 ≤ r.val) :
    PreservedRegs (regUpd reg r v) reg :=
  fun i hi => regUpd_fin_ne reg r i v (by omega)

lemma ParamsLoaded.of_preserved {n : ℕ} {reg₁ reg₀ : RegState EncR}
    (hp : ParamsLoaded n reg₀) (hpr : PreservedRegs reg₁ reg₀) : ParamsLoaded n reg₁ := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
  refine ⟨by rw [hpr _ (by decide), h0], by rw [hpr _ (by decide), h1],
    by rw [hpr _ (by decide), h2], by rw [hpr _ (by decide), h3],
    by rw [hpr _ (by decide), h4], by rw [hpr _ (by decide), h5],
    by rw [hpr _ (by decide), h6], by rw [hpr _ (by decide), h7],
    by rw [hpr _ (by decide), h8], by rw [hpr _ (by decide), h9],
    by rw [hpr _ (by decide), h10], by rw [hpr _ (by decide), h11],
    by rw [hpr _ (by decide), h12], by rw [hpr _ (by decide), h13],
    by rw [hpr _ (by decide), h14], by rw [hpr _ (by decide), h15],
    by rw [hpr _ (by decide), h16], by rw [hpr _ (by decide), h17],
    by rw [hpr _ (by decide), h18], by rw [hpr _ (by decide), h19],
    by rw [hpr _ (by decide), h20], by rw [hpr _ (by decide), h21],
    by rw [hpr _ (by decide), h22], by rw [hpr _ (by decide), h23],
    by rw [hpr _ (by decide), h24], by rw [hpr _ (by decide), h25],
    by rw [hpr _ (by decide), h26], by rw [hpr _ (by decide), h27],
    by rw [hpr _ (by decide), h28], by rw [hpr _ (by decide), h29],
    by rw [hpr _ (by decide), h30], by rw [hpr _ (by decide), h31],
    by rw [hpr _ (by decide), h32], by rw [hpr _ (by decide), h33]⟩

lemma paramL1_mul_paramL2 (d : ℕ) : paramL1 d * paramL2 d = paramL d := by
  unfold paramL1 paramL2 paramL
  rw [← pow_add]
  congr 1
  omega

lemma two_mul_treeM_le_treeVertOff (n : ℕ) :
    2 * treeM n ≤ treeVertOff (treeLog n + 1) (treeLog n + 2) := by
  rw [treeVertOff_net]
  have hlog1 : 1 ≤ treeLog n := le_max_left 1 _
  have hlt : treeLog n < treeM n := by
    unfold treeM; exact Nat.lt_two_pow_self
  have h2M : 2 ≤ treeM n := by
    unfold treeM
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ treeLog n := Nat.pow_le_pow_right (by decide) hlog1
  omega

lemma ovlTargetBit_eq (J blk p : ℕ) : ovlTargetBit J blk p = blk * J + p := by
  unfold ovlTargetBit
  split_ifs with h
  · rfl
  · have h1 : (blk + 1) * J = blk * J + J := by ring
    omega

/-! ### Pair Emitter (`rmEmitEndPair`) and Reusable Range-Loop Wrapper (`rmEdgeLoop_spec`) -/

abbrev RMEmitEndPairQ : Type := RMEmitUnaryQ ⊕ RMEmitUnaryQ

def rmEmitEndPair : RMProg EncR RMEmitEndPairQ :=
  rmChain (rmEmitUnary regEndU regS0) (rmEmitUnary regEndV regS0) rmEmitUnaryEntry

def rmEmitEndPairEntry : RMEmitEndPairQ := Sum.inl rmEmitUnaryEntry
def rmEmitEndPairExit : RMEmitEndPairQ := Sum.inr rmEmitUnaryExit

lemma rmEmitEndPair_spec (V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec rmEmitEndPair V inp rmEmitEndPairEntry reg rmEmitEndPairExit
      (regUpd reg regS0 0) (emitEdgeBits (reg regEndU, reg regEndV))
      (2 * reg regEndU + 2 * reg regEndV + 6) := by
  have hu := rmEmitUnary_spec regEndU regS0 (by decide) V inp reg hreg
  have hv := rmEmitUnary_spec regEndV regS0 (by decide) V inp (regUpd reg regS0 0) hu.reg₁_le
  rw [regUpd_ne reg (by decide) 0, regUpd_idem] at hv
  have hact : rmEmitUnary regEndU regS0 rmEmitUnaryEntry ≠ none := by
    simp [rmEmitUnary, rmEmitUnaryEntry, rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmChain, rmSeq, rmCopy]
  have hcomb := rmChain_spec_inl hact hu hv
  have hT : (2 * reg regEndU + 3) + (2 * reg regEndV + 3) = 2 * reg regEndU + 2 * reg regEndV + 6 := by
    omega
  rw [max_self, hT] at hcomb
  exact hcomb

lemma rmEdgeLoop_spec {Q : Type} (rCount : Fin EncR) (hic : regLoopI ≠ rCount)
    (body : RMProg EncR Q) (q₀ : Q) (V T_step : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (emitFn : ℕ → List Bool)
    (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hbody : ∀ (i : ℕ) (reg : RegState EncR),
      i < reg₀ rCount → PreservedRegs reg reg₀ → (∀ j, reg j ≤ V) → reg regLoopI = i →
      ∃ q₁ reg₁,
        PreservedRegs reg₁ reg ∧
        reg₁ regLoopI = i ∧
        reg₁ regLoopRem = reg regLoopRem ∧
        RMExec body V inp q₀ reg q₁ reg₁ (emitFn i) T_step) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec (rmForRange regLoopI regLoopRem rCount body q₀) V inp rmForRangeEntry reg₀
        rmForRangeExit reg₁ ((List.range (reg₀ rCount)).flatMap emitFn)
        (reg₀ rCount * (T_step + 2) + 3) := by
  let Inv : ℕ → RegState EncR → Prop := fun i reg =>
    PreservedRegs reg reg₀ ∧ (∀ j, reg j ≤ V) ∧ reg regLoopI = i
  have hInv_init : Inv 0 (regUpd (regUpd reg₀ regLoopI 0) regLoopRem (reg₀ rCount)) := by
    refine ⟨(PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
        (PreservedRegs.upd_ge _ regLoopI _ (by decide)),
      regUpd_le (regUpd_le hreg₀ regLoopI (Nat.zero_le V)) regLoopRem (hreg₀ rCount), ?_⟩
    simp
  have hInv_le : ∀ i reg, Inv i reg → ∀ j, reg j ≤ V := fun _ _ h => h.2.1
  have hInv_idx : ∀ i reg, Inv i reg → reg regLoopI = i := fun _ _ h => h.2.2
  have hInv_rem : ∀ i reg v, v ≤ V → Inv i reg → Inv i (regUpd reg regLoopRem v) := fun i reg v hv h =>
    ⟨(PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans h.1,
      regUpd_le h.2.1 regLoopRem hv, by simp [h.2.2]⟩
  have hstep : ∀ i reg, i < reg₀ rCount → Inv i reg →
      ∃ q₁ reg₁, reg₁ regLoopI = i ∧ reg₁ regLoopRem = reg regLoopRem ∧
        Inv (i + 1) (regUpd reg₁ regLoopI (i + 1)) ∧
        RMExec body V inp q₀ reg q₁ reg₁ (emitFn i) T_step := by
    intro i reg hi hInv
    rcases hbody i reg hi hInv.1 hInv.2.1 hInv.2.2 with ⟨q₁, reg₁, hpr₁, hi₁, hrem₁, hex⟩
    refine ⟨q₁, reg₁, hi₁, hrem₁, ?_, hex⟩
    refine ⟨(PreservedRegs.upd_ge _ regLoopI _ (by decide)).trans (hpr₁.trans hInv.1),
      regUpd_le hex.reg₁_le regLoopI (by have := hreg₀ rCount; omega), by simp⟩
  rcases rmForRange_spec regLoopI regLoopRem rCount (by decide) hic body q₀ V T_step inp reg₀
      Inv emitFn hreg₀ hInv_init hInv_le hInv_idx hInv_rem hstep
    with ⟨reg₁, _, _, hInv_end, hex⟩
  exact ⟨reg₁, hInv_end.1, hex⟩

/-! ### 14-Block FlatMap Decomposition of `rawEnds` -/

lemma flatMap_range_add {α : Type*} (f : ℕ → List α) (a b : ℕ) :
    (List.range (a + b)).flatMap f =
      (List.range a).flatMap f ++ (List.range b).flatMap (fun k => f (a + k)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
        List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

lemma list_flatMap_range_congr {α : Type*} (m : ℕ) {f g : ℕ → List α}
    (h : ∀ k < m, f k = g k) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  apply List.flatMap_congr
  intro k hk
  rw [List.mem_range] at hk
  exact h k hk

lemma flatMap_range_rawEnds_eq (n : ℕ) :
    (List.range (netEdgeCount n)).flatMap (fun e => emitEdgeBits (rawEnds n e)) =
      (((List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB0 n e)) ++
        (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB1 n e))) ++
       ((List.range (2 * treeM n)).flatMap (fun e => emitEdgeBits (endsB2 n e)) ++
        (List.range n).flatMap (fun e => emitEdgeBits (endsB3 n e)))) ++
      ((((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB4 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB5 n e))) ++
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB6 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB7 n e)))) ++
       (((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB8 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB9 n e))) ++
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB10 n e)) ++
         (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB11 n e)))) ++
       ((List.range (treeEdgeOff (treeLog n + 1) (treeLog n + 2))).flatMap
          (fun e => emitEdgeBits (endsB12 n e)) ++
        (List.range (treeLog n + 3)).flatMap (fun e => emitEdgeBits (endsB13 n e)))) := by
  have hsplit : ∀ (a b : ℕ), (List.range (a + b)).flatMap (fun e => emitEdgeBits (rawEnds n e)) =
      (List.range a).flatMap (fun e => emitEdgeBits (rawEnds n e)) ++
      (List.range b).flatMap (fun k => emitEdgeBits (rawEnds n (a + k))) :=
    fun a b => flatMap_range_add _ a b
  have hE1 : netE1 n = 2 * n := rfl
  have hE2 : netE2 n = netE1 n + 2 * n := by simp [netE2, netE1]; omega
  have hE3 : netE3 n = netE2 n + 2 * treeM n := by simp [netE3, netE2]
  have hE4 : netE4 n = netE3 n + n := rfl
  have hE5 : netE5 n = netE4 n + 2 * paramJ n * paramL n := rfl
  have hE6 : netE6 n = netE5 n + 2 * paramJ n * paramL n := rfl
  have hE7 : netE7 n = netE6 n + 2 * paramJ n * paramL n := rfl
  have hE8 : netE8 n = netE7 n + 2 * paramJ n * paramL n := rfl
  have hE9 : netE9 n = netE8 n + 2 * paramJ n * paramL n := rfl
  have hE10 : netE10 n = netE9 n + 2 * paramJ n * paramL n := rfl
  have hE11 : netE11 n = netE10 n + 2 * paramJ n * paramL n := rfl
  have hE12 : netE12 n = netE11 n + 2 * n := rfl
  have hE13 : netE13 n = netE12 n + treeEdgeOff (treeLog n + 1) (treeLog n + 2) := rfl
  have hEC : netEdgeCount n = netE13 n + (treeLog n + 3) := rfl
  have hb0 : (List.range (2 * n)).flatMap (fun e => emitEdgeBits (rawEnds n e)) =
      (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB0 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by simp [rawEnds, netE1, hk])
  have hb1 : (List.range (2 * n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE1 n + k))) =
      (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB1 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE1 n + k < netE1 n) by omega, show netE1 n + k < netE2 n by omega])
  have hb2 : (List.range (2 * treeM n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE2 n + k))) =
      (List.range (2 * treeM n)).flatMap (fun e => emitEdgeBits (endsB2 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE2 n + k < netE1 n) by omega, show ¬ (netE2 n + k < netE2 n) by omega,
        show netE2 n + k < netE3 n by omega])
  have hb3 : (List.range n).flatMap (fun k => emitEdgeBits (rawEnds n (netE3 n + k))) =
      (List.range n).flatMap (fun e => emitEdgeBits (endsB3 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE3 n + k < netE1 n) by omega, show ¬ (netE3 n + k < netE2 n) by omega,
        show ¬ (netE3 n + k < netE3 n) by omega, show netE3 n + k < netE4 n by omega])
  have hb4 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE4 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB4 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE4 n + k < netE1 n) by omega, show ¬ (netE4 n + k < netE2 n) by omega,
        show ¬ (netE4 n + k < netE3 n) by omega, show ¬ (netE4 n + k < netE4 n) by omega,
        show netE4 n + k < netE5 n by omega])
  have hb5 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE5 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB5 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE5 n + k < netE1 n) by omega, show ¬ (netE5 n + k < netE2 n) by omega,
        show ¬ (netE5 n + k < netE3 n) by omega, show ¬ (netE5 n + k < netE4 n) by omega,
        show ¬ (netE5 n + k < netE5 n) by omega, show netE5 n + k < netE6 n by omega])
  have hb6 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE6 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB6 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE6 n + k < netE1 n) by omega, show ¬ (netE6 n + k < netE2 n) by omega,
        show ¬ (netE6 n + k < netE3 n) by omega, show ¬ (netE6 n + k < netE4 n) by omega,
        show ¬ (netE6 n + k < netE5 n) by omega, show ¬ (netE6 n + k < netE6 n) by omega,
        show netE6 n + k < netE7 n by omega])
  have hb7 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE7 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB7 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE7 n + k < netE1 n) by omega, show ¬ (netE7 n + k < netE2 n) by omega,
        show ¬ (netE7 n + k < netE3 n) by omega, show ¬ (netE7 n + k < netE4 n) by omega,
        show ¬ (netE7 n + k < netE5 n) by omega, show ¬ (netE7 n + k < netE6 n) by omega,
        show ¬ (netE7 n + k < netE7 n) by omega, show netE7 n + k < netE8 n by omega])
  have hb8 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE8 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB8 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE8 n + k < netE1 n) by omega, show ¬ (netE8 n + k < netE2 n) by omega,
        show ¬ (netE8 n + k < netE3 n) by omega, show ¬ (netE8 n + k < netE4 n) by omega,
        show ¬ (netE8 n + k < netE5 n) by omega, show ¬ (netE8 n + k < netE6 n) by omega,
        show ¬ (netE8 n + k < netE7 n) by omega, show ¬ (netE8 n + k < netE8 n) by omega,
        show netE8 n + k < netE9 n by omega])
  have hb9 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE9 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB9 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE9 n + k < netE1 n) by omega, show ¬ (netE9 n + k < netE2 n) by omega,
        show ¬ (netE9 n + k < netE3 n) by omega, show ¬ (netE9 n + k < netE4 n) by omega,
        show ¬ (netE9 n + k < netE5 n) by omega, show ¬ (netE9 n + k < netE6 n) by omega,
        show ¬ (netE9 n + k < netE7 n) by omega, show ¬ (netE9 n + k < netE8 n) by omega,
        show ¬ (netE9 n + k < netE9 n) by omega, show netE9 n + k < netE10 n by omega])
  have hb10 : (List.range (2 * paramJ n * paramL n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE10 n + k))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB10 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE10 n + k < netE1 n) by omega, show ¬ (netE10 n + k < netE2 n) by omega,
        show ¬ (netE10 n + k < netE3 n) by omega, show ¬ (netE10 n + k < netE4 n) by omega,
        show ¬ (netE10 n + k < netE5 n) by omega, show ¬ (netE10 n + k < netE6 n) by omega,
        show ¬ (netE10 n + k < netE7 n) by omega, show ¬ (netE10 n + k < netE8 n) by omega,
        show ¬ (netE10 n + k < netE9 n) by omega, show ¬ (netE10 n + k < netE10 n) by omega,
        show netE10 n + k < netE11 n by omega])
  have hb11 : (List.range (2 * n)).flatMap (fun k => emitEdgeBits (rawEnds n (netE11 n + k))) =
      (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB11 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE11 n + k < netE1 n) by omega, show ¬ (netE11 n + k < netE2 n) by omega,
        show ¬ (netE11 n + k < netE3 n) by omega, show ¬ (netE11 n + k < netE4 n) by omega,
        show ¬ (netE11 n + k < netE5 n) by omega, show ¬ (netE11 n + k < netE6 n) by omega,
        show ¬ (netE11 n + k < netE7 n) by omega, show ¬ (netE11 n + k < netE8 n) by omega,
        show ¬ (netE11 n + k < netE9 n) by omega, show ¬ (netE11 n + k < netE10 n) by omega,
        show ¬ (netE11 n + k < netE11 n) by omega, show netE11 n + k < netE12 n by omega])
  have hb12 : (List.range (treeEdgeOff (treeLog n + 1) (treeLog n + 2))).flatMap
        (fun k => emitEdgeBits (rawEnds n (netE12 n + k))) =
      (List.range (treeEdgeOff (treeLog n + 1) (treeLog n + 2))).flatMap
        (fun e => emitEdgeBits (endsB12 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE12 n + k < netE1 n) by omega, show ¬ (netE12 n + k < netE2 n) by omega,
        show ¬ (netE12 n + k < netE3 n) by omega, show ¬ (netE12 n + k < netE4 n) by omega,
        show ¬ (netE12 n + k < netE5 n) by omega, show ¬ (netE12 n + k < netE6 n) by omega,
        show ¬ (netE12 n + k < netE7 n) by omega, show ¬ (netE12 n + k < netE8 n) by omega,
        show ¬ (netE12 n + k < netE9 n) by omega, show ¬ (netE12 n + k < netE10 n) by omega,
        show ¬ (netE12 n + k < netE11 n) by omega, show ¬ (netE12 n + k < netE12 n) by omega,
        show netE12 n + k < netE13 n by omega])
  have hb13 : (List.range (treeLog n + 3)).flatMap (fun k => emitEdgeBits (rawEnds n (netE13 n + k))) =
      (List.range (treeLog n + 3)).flatMap (fun e => emitEdgeBits (endsB13 n e)) :=
    list_flatMap_range_congr _ (fun k hk => by
      simp [rawEnds, show ¬ (netE13 n + k < netE1 n) by omega, show ¬ (netE13 n + k < netE2 n) by omega,
        show ¬ (netE13 n + k < netE3 n) by omega, show ¬ (netE13 n + k < netE4 n) by omega,
        show ¬ (netE13 n + k < netE5 n) by omega, show ¬ (netE13 n + k < netE6 n) by omega,
        show ¬ (netE13 n + k < netE7 n) by omega, show ¬ (netE13 n + k < netE8 n) by omega,
        show ¬ (netE13 n + k < netE9 n) by omega, show ¬ (netE13 n + k < netE10 n) by omega,
        show ¬ (netE13 n + k < netE11 n) by omega, show ¬ (netE13 n + k < netE12 n) by omega,
        show ¬ (netE13 n + k < netE13 n) by omega])
  rw [hEC, hsplit, hb13, hE13, hsplit, hb12, hE12, hsplit, hb11, hE11, hsplit, hb10,
      hE10, hsplit, hb9, hE9, hsplit, hb8, hE8, hsplit, hb7, hE7, hsplit, hb6,
      hE6, hsplit, hb5, hE5, hsplit, hb4, hE4, hsplit, hb3, hE3, hsplit, hb2,
      hE2, hsplit, hb1, hE1, hb0]
  simp only [List.append_assoc]

/-! ### Edge Block Emitters B0, B1, B2, B3 -/

/-- Block B0 (`2n` edges): `(e, netV1 n + e)`. -/
abbrev RMB0BodyQ : Type := Bool ⊕ (RMSetAddQ ⊕ RMEmitEndPairQ)
abbrev RMEmitB0Q : Type := RMForRangeQ RMB0BodyQ

def rmB0Body : RMProg EncR RMB0BodyQ :=
  rmChain (rmCopy regEndU regLoopI)
    (rmChain (rmSetAdd regEndV regV1 regLoopI) rmEmitEndPair rmEmitEndPairEntry)
    (Sum.inl rmSetAddEntry)

def rmB0BodyEntry : RMB0BodyQ := Sum.inl false

def rmEmitB0 : RMProg EncR RMEmitB0Q :=
  rmForRange regLoopI regLoopRem regV1 rmB0Body rmB0BodyEntry

lemma rmEmitB0_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (_hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB0 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB0 n e)))
        (40 * n ^ 2 + 30 * n + 10) := by
  have hcnt : reg₀ regV1 = 2 * n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases rmEdgeLoop_spec regV1 (by decide) rmB0Body rmB0BodyEntry V (16 * n + 10) inp reg₀
      (fun e => emitEdgeBits (endsB0 n e)) hreg₀ (by
        intro i reg hi hpr hreg hI
        have hV1 : reg regV1 = 2 * n := by rw [hpr regV1 (by decide), hcnt]
        have hi' : i < 2 * n := by omega
        have hc := rmCopy_spec regEndU regLoopI V inp reg hreg
        set r1 := regUpd reg regEndU (reg regLoopI)
        have ha := rmSetAdd_spec regEndV regV1 regLoopI (by decide) (by decide) (by decide)
          V inp r1 hc.reg₁_le (by simp [r1, hV1, hI]; omega)
        set r2 := regUpd (regUpd r1 regEndV (r1 regV1 + r1 regLoopI)) regS0 0
        have he := rmEmitEndPair_spec V inp r2 ha.reg₁_le
        have hr2U : r2 regEndU = i := by simp [r2, r1, hI]
        have hr2V : r2 regEndV = netV1 n + i := by simp [r2, r1, hV1, hI, netV1]
        have hcomb := rmChain_spec_inl (by simp [rmCopy]) hc
          (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha he)
        have hT : 1 + (2 * r1 regLoopI + 3 + (2 * r2 regEndU + 2 * r2 regEndV + 6)) ≤ 16 * n + 10 := by
          have hr1I : r1 regLoopI = i := by simp [r1, hI]
          rw [hr1I, hr2U, hr2V]; simp only [netV1]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 16 * n + 10) (by simp) hT
        simp only [List.nil_append, hr2U, hr2V] at hfin
        refine ⟨Sum.inr (Sum.inr rmEmitEndPairExit), regUpd r2 regS0 0, ?_, by simp [r2, r1, hI], by simp [r2, r1], ?_⟩
        · exact (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans
            ((PreservedRegs.upd_ge _ regS0 _ (by decide)).trans
              ((PreservedRegs.upd_ge _ regEndV _ (by decide)).trans
                (PreservedRegs.upd_ge _ regEndU _ (by decide))))
        · simpa [endsB0, netV0, rmB0Body, rmB0BodyEntry] using hfin)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * n * (16 * n + 10 + 2) + 3 ≤ 40 * n ^ 2 + 30 * n + 10 := by
    have : 2 * n * (16 * n + 10 + 2) + 3 = 32 * n ^ 2 + 24 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 40 * n ^ 2 + 30 * n + 10) (le_refl _) hT⟩

/-- Block B1 (`2n` edges): `(netV1 n + i, if i < n then netV12 n + i else netV5 n + ((i - n) / J) % L2)`. -/
abbrev RMB1ElseQ : Type := Bool ⊕ (RMSubQ ⊕ (RMDivModQ ⊕ (RMDivModQ ⊕ RMSetAddQ)))
abbrev RMB1IfQ : Type := Option Bool ⊕ (RMB1ElseQ ⊕ (Bool ⊕ RMSetAddQ))
abbrev RMB1BodyQ : Type := RMSetAddQ ⊕ (Fin 8 ⊕ (RMB1IfQ ⊕ RMEmitEndPairQ))
abbrev RMEmitB1Q : Type := RMForRangeQ RMB1BodyQ

def rmB1Else : RMProg EncR RMB1ElseQ :=
  rmChain (rmCopy regS1 regLoopI)
    (rmChain (rmSub regS1 regN regS2)
      (rmChain (rmDivMod regS3 regS2 regS1 regJ regS4 regS5 regS6)
        (rmChain (rmDivMod regS1 regS2 regS3 regL2 regS4 regS5 regS6)
          (rmSetAdd regEndV regV5 regS2) rmSetAddEntry)
        (Sum.inl rmDivModEntry))
      (Sum.inl rmDivModEntry))
    (Sum.inl rmSubEntry)

def rmB1ElseEntry : RMB1ElseQ := Sum.inl false

def rmB1Body : RMProg EncR RMB1BodyQ :=
  rmChain (rmSetAdd regEndU regV1 regLoopI)
    (rmChain (rmCmpLt regS0 regLoopI regN regS1 regS2)
      (rmChain (rmIfZero regS0 rmB1Else (rmSetAdd regEndV regV12 regLoopI) rmB1ElseEntry rmSetAddEntry)
        rmEmitEndPair rmEmitEndPairEntry)
      (Sum.inl rmIfZeroEntry))
    (Sum.inl 0)

def rmB1BodyEntry : RMB1BodyQ := Sum.inl rmSetAddEntry

def rmEmitB1 : RMProg EncR RMEmitB1Q :=
  rmForRange regLoopI regLoopRem regV1 rmB1Body rmB1BodyEntry

lemma rmEmitB1_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB1 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB1 n e)))
        (5000 * n ^ 2 + 500 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL2_pos : 0 < paramL2 n := one_le_paramL2 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) (paramL_le_27_mul hn)
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hv12_lt : netV12 n + n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13]; omega
  have hv5_lt : netV5 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV5]; omega
  have hcnt : reg₀ regV1 = 2 * n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases rmEdgeLoop_spec regV1 (by decide) rmB1Body rmB1BodyEntry V (2200 * n + 200) inp reg₀
      (fun e => emitEdgeBits (endsB1 n e)) hreg₀ (by
        intro i reg hi hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hN : reg regN = n := hp'.1
        have hJ : reg regJ = paramJ n := hp'.2.2.1
        have hL2 : reg regL2 = paramL2 n := hp'.2.2.2.2.2.2.2.1
        have hV1 : reg regV1 = netV1 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV5 : reg regV5 = netV5 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV12 : reg regV12 = netV12 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hi' : i < 2 * n := by omega
        have haU := rmSetAdd_spec regEndU regV1 regLoopI (by decide) (by decide) (by decide)
          V inp reg hreg (by rw [hV1, hI]; simp only [netV1]; omega)
        set r1 := regUpd (regUpd reg regEndU (reg regV1 + reg regLoopI)) regS0 0
        have h1_I : r1 regLoopI = i := by simp [r1, hI]
        have h1_N : r1 regN = n := by simp [r1, hN]
        have h1_U : r1 regEndU = netV1 n + i := by simp [r1, hV1, hI]
        have h1_pr : PreservedRegs r1 reg :=
          (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (PreservedRegs.upd_ge _ regEndU _ (by decide))
        rcases rmCmpLt_spec regS0 regLoopI regN regS1 regS2 (by decide) (by decide) (by decide) (by decide)
            V inp r1 haU.reg₁_le h1V with ⟨r2, h2_fl, h2_fr, hcmp⟩
        have h2_U : r2 regEndU = netV1 n + i := by rw [h2_fr regEndU (by decide) (by decide) (by decide), h1_U]
        have h2_I : r2 regLoopI = i := by rw [h2_fr regLoopI (by decide) (by decide) (by decide), h1_I]
        have h2_rem : r2 regLoopRem = reg regLoopRem := by
          rw [h2_fr regLoopRem (by decide) (by decide) (by decide)]; simp [r1]
        have h2_pr : PreservedRegs r2 reg := fun k hk => by
          rw [h2_fr k (by intro h; subst h; simp at hk) (by intro h; subst h; simp at hk)
            (by intro h; subst h; simp at hk), h1_pr k hk]
        have hbranch : ∃ qB r3,
            PreservedRegs r3 r2 ∧ r3 regLoopI = i ∧ r3 regLoopRem = r2 regLoopRem ∧
            r3 regEndU = netV1 n + i ∧
            r3 regEndV = (if i < n then netV12 n + i else netV5 n + (((i - n) / paramJ n) % paramL2 n)) ∧
            RMExec (rmIfZero regS0 rmB1Else (rmSetAdd regEndV regV12 regLoopI) rmB1ElseEntry rmSetAddEntry)
              V inp rmIfZeroEntry r2 qB r3 [] (160 * n + 40) := by
          by_cases hlt : i < n
          · have hfl : r2 regS0 ≠ 0 := by rw [h2_fl, h1_I, h1_N]; simp [hlt]
            have h2_V12 : r2 regV12 = netV12 n := by rw [h2_pr regV12 (by decide), hV12]
            have hth := rmSetAdd_spec regEndV regV12 regLoopI (by decide) (by decide) (by decide)
              V inp r2 hcmp.reg₁_le (by rw [h2_V12, h2_I]; omega)
            have hif := (rmIfZero_pos_spec regS0 rmB1Else rmB1ElseEntry hfl hth).weaken
              (V₂ := V) (T₂ := 160 * n + 40) (le_refl _) (by rw [h2_I]; omega)
            refine ⟨_, _, (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans
                (PreservedRegs.upd_ge _ regEndV _ (by decide)),
              by simp [h2_I], by simp, by simp [h2_U], by simp [hlt, h2_V12, h2_I], hif⟩
          · have hfl : r2 regS0 = 0 := by rw [h2_fl, h1_I, h1_N]; simp [hlt]
            have h2_N : r2 regN = n := by rw [h2_pr regN (by decide), hN]
            have h2_J : r2 regJ = paramJ n := by rw [h2_pr regJ (by decide), hJ]
            have h2_L2 : r2 regL2 = paramL2 n := by rw [h2_pr regL2 (by decide), hL2]
            have h2_V5 : r2 regV5 = netV5 n := by rw [h2_pr regV5 (by decide), hV5]
            have hc1 := rmCopy_spec regS1 regLoopI V inp r2 hcmp.reg₁_le
            set s1 := regUpd r2 regS1 (r2 regLoopI)
            have hs2 := rmSub_spec regS1 regN regS2 (by decide) V inp s1 hc1.reg₁_le
            set s2 := regUpd (regUpd s1 regS1 (s1 regS1 - s1 regN)) regS2 0
            have hs2_S1 : s2 regS1 = i - n := by simp [s2, s1, h2_I, h2_N]
            have hs2_J : s2 regJ = paramJ n := by simp [s2, s1, h2_J]
            rcases rmDivMod_spec regS3 regS2 regS1 regJ regS4 regS5 regS6
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide)
                V inp s2 (by rw [hs2_J]; exact hJ_pos) hs2.reg₁_le h1V
              with ⟨s3, hs3_q, _, hs3_fr, hd3⟩
            have hs3_L2 : s3 regL2 = paramL2 n := by
              rw [hs3_fr regL2 (by decide) (by decide) (by decide) (by decide) (by decide)]
              simp [s2, s1, h2_L2]
            have hs3_q' : s3 regS3 = (i - n) / paramJ n := by rw [hs3_q, hs2_S1, hs2_J]
            rcases rmDivMod_spec regS1 regS2 regS3 regL2 regS4 regS5 regS6
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide)
                V inp s3 (by rw [hs3_L2]; exact hL2_pos) hd3.reg₁_le h1V
              with ⟨s4, _, hs4_r, hs4_fr, hd4⟩
            have hs4_r' : s4 regS2 = ((i - n) / paramJ n) % paramL2 n := by rw [hs4_r, hs3_q', hs3_L2]
            have hs4_V5 : s4 regV5 = netV5 n := by
              rw [hs4_fr regV5 (by decide) (by decide) (by decide) (by decide) (by decide),
                  hs3_fr regV5 (by decide) (by decide) (by decide) (by decide) (by decide)]
              simp [s2, s1, h2_V5]
            have hmod_lt : ((i - n) / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2_pos
            have ha5 := rmSetAdd_spec regEndV regV5 regS2 (by decide) (by decide) (by decide)
              V inp s4 hd4.reg₁_le (by rw [hs4_V5, hs4_r']; omega)
            set s5 := regUpd (regUpd s4 regEndV (s4 regV5 + s4 regS2)) regS0 0
            have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
              intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
            have helse := rmChain_spec_inl (by simp [rmCopy]) hc1
              (rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs2
                (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd3
                  (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd4 ha5)))
            have hdiv_le : (i - n) / paramJ n ≤ n := le_trans (Nat.div_le_self _ _) (by omega)
            have hT_e : 2 + (1 + (2 * s1 regN + 2 + (15 * s2 regS1 + 2 * s2 regJ + 10 +
                (15 * s3 regS3 + 2 * s3 regL2 + 10 + (2 * s4 regS2 + 3))))) ≤ 160 * n + 40 := by
              have hs1_N : s1 regN = n := by simp [s1, h2_N]
              rw [hs1_N, hs2_S1, hs2_J, hs3_q', hs3_L2, hs4_r']
              omega
            have hif := (rmIfZero_zero_spec regS0 (rmSetAdd regEndV regV12 regLoopI) rmSetAddEntry hfl helse).weaken
              (V₂ := V) (T₂ := 160 * n + 40) (by simp) hT_e
            simp only [List.nil_append] at hif
            have hs5_pr : PreservedRegs s5 r2 := fun k hk => by
              have hne : ∀ r : Fin EncR, 41 ≤ r.val → k ≠ r := fun r hr heq => by subst heq; omega
              dsimp only [s5]
              rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regEndV (by decide)),
                  hs4_fr k (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS4 (by decide))
                    (hne regS5 (by decide)) (hne regS6 (by decide)),
                  hs3_fr k (hne regS3 (by decide)) (hne regS2 (by decide)) (hne regS4 (by decide))
                    (hne regS5 (by decide)) (hne regS6 (by decide))]
              dsimp only [s2, s1]
              rw [regUpd_ne _ (hne regS2 (by decide)), regUpd_ne _ (hne regS1 (by decide)),
                  regUpd_ne _ (hne regS1 (by decide))]
            have hs5_keep : ∀ k : Fin EncR, k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → s5 k = r2 k := by
              intro k hk
              have hne : ∀ r : Fin EncR, r.val ≤ 48 ∨ r = regEndV → k ≠ r := by
                rcases hk with rfl | rfl | rfl <;> (intro r hr heq; subst heq; rcases hr with hr | hr <;> simp at hr)
              dsimp only [s5]
              rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndV (Or.inr rfl)),
                  hs4_fr k (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                    (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))),
                  hs3_fr k (hne regS3 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                    (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide)))]
              dsimp only [s2, s1]
              rw [regUpd_ne _ (hne regS2 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
                  regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
            refine ⟨_, s5, hs5_pr,
              by rw [hs5_keep regLoopI (Or.inl rfl), h2_I],
              hs5_keep regLoopRem (Or.inr (Or.inl rfl)),
              by rw [hs5_keep regEndU (Or.inr (Or.inr rfl)), h2_U],
              by simp [s5, hlt, hs4_V5, hs4_r'], hif⟩
        rcases hbranch with ⟨qB, r3, h3_pr, h3_I, h3_rem, h3_U, h3_V, hif⟩
        have he := rmEmitEndPair_spec V inp r3 hif.reg₁_le
        have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) haU
          (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp
            (rmChain_spec_inl (by simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]) hif he))
        have hU_le : r3 regEndU ≤ 4 * n := by rw [h3_U]; simp only [netV1]; omega
        have hV_le : r3 regEndV ≤ 500 * n + 20 := by
          rw [h3_V]; split_ifs with hlt
          · omega
          · have : ((i - n) / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2_pos; omega
        have hT : (2 * reg regLoopI + 3) + ((2 * min (r1 regLoopI) (r1 regN) + 6) +
            ((160 * n + 40) + (2 * r3 regEndU + 2 * r3 regEndV + 6))) ≤ 2200 * n + 200 := by
          rw [hI, h1_I, h1_N]
          have : min i n ≤ n := min_le_right _ _
          omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2200 * n + 200) (by simp) hT
        simp only [List.nil_append, h3_U, h3_V] at hfin
        refine ⟨_, _, (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (h3_pr.trans h2_pr),
          by simp [h3_I], by simp [h3_rem, h2_rem], hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * n * (2200 * n + 200 + 2) + 3 ≤ 5000 * n ^ 2 + 500 * n + 10 := by
    have : 2 * n * (2200 * n + 200 + 2) + 3 = 4400 * n ^ 2 + 404 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 5000 * n ^ 2 + 500 * n + 10) (le_refl _) hT⟩

/-- Block B2 (`2 * treeM n` edges): leaf-to-tree edges `endsB2`. -/
abbrev RMB2DstQ : Type := RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ Bool)))
abbrev RMB2Br3ElseQ : Type := Bool ⊕ (RMSubQ ⊕ RMSetAddQ)
abbrev RMB2Br3ThenQ : Type := Bool ⊕ (RMSubQ ⊕ (RMSetAddQ ⊕ RMSetAddQ))
abbrev RMB2Br3Q : Type := Fin 8 ⊕ (Option Bool ⊕ (RMB2Br3ElseQ ⊕ (Bool ⊕ RMB2Br3ThenQ)))
abbrev RMB2Br2ThenQ : Type := Bool ⊕ (RMSubQ ⊕ RMSetAddQ)
abbrev RMB2Br2Q : Type := Fin 8 ⊕ (Option Bool ⊕ (RMB2Br3Q ⊕ (Bool ⊕ RMB2Br2ThenQ)))
abbrev RMB2SrcQ : Type := RMSetAddQ ⊕ (Fin 8 ⊕ (Option Bool ⊕ (RMB2Br2Q ⊕ (Bool ⊕ RMSetAddQ))))
abbrev RMB2BodyQ : Type := RMB2DstQ ⊕ (RMB2SrcQ ⊕ RMEmitEndPairQ)
abbrev RMEmitB2Q : Type := RMSetAddQ ⊕ RMForRangeQ RMB2BodyQ

def rmB2Dst : RMProg EncR RMB2DstQ :=
  rmChain (rmSetConst regS0 2)
    (rmChain (rmDivMod regS1 regS2 regLoopI regS0 regS3 regS4 regS5)
      (rmChain (rmSetAdd regS3 regS1 regS1)
        (rmChain (rmSetAdd regEndV regV15 regS3) (rmInc regEndV) false)
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmB2DstEntry : RMB2DstQ := Sum.inl rmSetConstEntry

def rmB2Br3Else : RMProg EncR RMB2Br3ElseQ :=
  rmChain (rmCopy regS1 regLoopI)
    (rmChain (rmSub regS1 regS7 regS2) (rmSetAdd regEndU regV14 regS1) rmSetAddEntry)
    (Sum.inl rmSubEntry)

def rmB2Br3Then : RMProg EncR RMB2Br3ThenQ :=
  rmChain (rmCopy regS1 regLoopI)
    (rmChain (rmSub regS1 regTreeM regS2)
      (rmChain (rmSetAdd regS3 regV1 regN) (rmSetAdd regEndU regS3 regS1) rmSetAddEntry)
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmSubEntry)

def rmB2Br3 : RMProg EncR RMB2Br3Q :=
  rmChain (rmCmpLt regS0 regLoopI regS7 regS1 regS2)
    (rmIfZero regS0 rmB2Br3Else rmB2Br3Then (Sum.inl false) (Sum.inl false))
    rmIfZeroEntry

def rmB2Br2Then : RMProg EncR RMB2Br2ThenQ :=
  rmChain (rmCopy regS1 regLoopI)
    (rmChain (rmSub regS1 regN regS2) (rmSetAdd regEndU regV13 regS1) rmSetAddEntry)
    (Sum.inl rmSubEntry)

def rmB2Br2 : RMProg EncR RMB2Br2Q :=
  rmChain (rmCmpLt regS0 regLoopI regTreeM regS1 regS2)
    (rmIfZero regS0 rmB2Br3 rmB2Br2Then (Sum.inl 0) (Sum.inl false))
    rmIfZeroEntry

def rmB2Src : RMProg EncR RMB2SrcQ :=
  rmChain (rmSetAdd regS7 regTreeM regN)
    (rmChain (rmCmpLt regS0 regLoopI regN regS1 regS2)
      (rmIfZero regS0 rmB2Br2 (rmSetAdd regEndU regV1 regLoopI) (Sum.inl 0) rmSetAddEntry)
      rmIfZeroEntry)
    (Sum.inl 0)

def rmB2SrcEntry : RMB2SrcQ := Sum.inl rmSetAddEntry

def rmB2Body : RMProg EncR RMB2BodyQ :=
  rmChain rmB2Dst (rmChain rmB2Src rmEmitEndPair rmEmitEndPairEntry) (Sum.inl rmB2SrcEntry)

def rmB2BodyEntry : RMB2BodyQ := Sum.inl rmB2DstEntry

def rmEmitB2 : RMProg EncR RMEmitB2Q :=
  rmChain (rmSetAdd regLoopJ regTreeM regTreeM)
    (rmForRange regLoopI regLoopRem regLoopJ rmB2Body rmB2BodyEntry)
    rmForRangeEntry

def rmEmitB2Entry : RMEmitB2Q := Sum.inl rmSetAddEntry
def rmEmitB2Exit : RMEmitB2Q := Sum.inr rmForRangeExit

lemma rmB2Dst_spec (n V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ j, reg j ≤ V)
    (hV : 500 * n + 20 ≤ V) (hI : reg regLoopI < 2 * treeM n) :
    ∃ r1 : RegState EncR,
      PreservedRegs r1 reg ∧
      r1 regLoopI = reg regLoopI ∧
      r1 regLoopRem = reg regLoopRem ∧
      r1 regEndV = netV15 n + (reg regLoopI / 2) * 2 + 1 ∧
      RMExec rmB2Dst V inp rmB2DstEntry reg (Sum.inr (Sum.inr (Sum.inr (Sum.inr true)))) r1 []
        (100 * n + 40) := by
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hV15 : reg regV15 = netV15 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2M_vo : 2 * treeM n ≤ treeVertOff (treeLog n + 1) (treeLog n + 2) := two_mul_treeM_le_treeVertOff n
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hv16_le : netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16]; omega
  set leaf := reg regLoopI
  have hs0 := rmSetConst_spec regS0 2 V inp reg hreg (by omega)
  set s1 := regUpd reg regS0 2
  rcases rmDivMod_spec regS1 regS2 regLoopI regS0 regS3 regS4 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      V inp s1 (by simp [s1]) hs0.reg₁_le h1V
    with ⟨s2, hs2_q, _, hs2_fr, hd2⟩
  have hs2_q' : s2 regS1 = leaf / 2 := by rw [hs2_q]; simp [s1, leaf]
  have hs2_V15 : s2 regV15 = netV15 n := by
    rw [hs2_fr regV15 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s1, hV15]
  have ha3 := rmSetAdd_spec regS3 regS1 regS1 (by decide) (by decide) (by decide)
    V inp s2 hd2.reg₁_le (by rw [hs2_q']; omega)
  set s3 := regUpd (regUpd s2 regS3 (s2 regS1 + s2 regS1)) regS0 0
  have hs3_S3 : s3 regS3 = (leaf / 2) * 2 := by simp [s3, hs2_q']; omega
  have hs3_V15 : s3 regV15 = netV15 n := by simp [s3, hs2_V15]
  have ha4 := rmSetAdd_spec regEndV regV15 regS3 (by decide) (by decide) (by decide)
    V inp s3 ha3.reg₁_le (by rw [hs3_V15, hs3_S3]; omega)
  set s4 := regUpd (regUpd s3 regEndV (s3 regV15 + s3 regS3)) regS0 0
  have hi5 := rmInc_spec regEndV V inp s4 ha4.reg₁_le (by simp [s4, hs3_V15, hs3_S3]; omega)
  set s5 := regUpd s4 regEndV (s4 regEndV + 1)
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hs0
    (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd2
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha3
        (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha4 hi5)))
  have hT : 1 + 2 + (15 * s1 regLoopI + 2 * s1 regS0 + 10 + (2 * s2 regS1 + 3 + (2 * s3 regS3 + 3 + 1))) ≤
      100 * n + 40 := by
    have h1I : s1 regLoopI = leaf := by simp [s1, leaf]
    have h1S0 : s1 regS0 = 2 := by simp [s1]
    rw [h1I, h1S0, hs2_q', hs3_S3]; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 100 * n + 40) (by simp) hT
  simp only [List.nil_append] at hfin
  have hkeep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem → s5 k = reg k := by
    intro k hk
    have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndV → k ≠ r := by
      intro r hr heq
      have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
    dsimp only [s5, s4, s3]
    rw [regUpd_ne _ (hne regEndV (Or.inr rfl)), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
        regUpd_ne _ (hne regEndV (Or.inr rfl)), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
        regUpd_ne _ (hne regS3 (Or.inl (by decide))),
        hs2_fr k (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
          (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
    dsimp only [s1]; rw [regUpd_ne _ (hne regS0 (Or.inl (by decide)))]
  refine ⟨s5, fun k hk => hkeep k (Or.inl hk), hkeep regLoopI (Or.inr (Or.inl rfl)),
    hkeep regLoopRem (Or.inr (Or.inr rfl)), by simp [s5, s4, hs3_V15, hs3_S3], hfin⟩

lemma rmB2Br3_spec (n V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ j, reg j ≤ V)
    (hV : 500 * n + 20 ≤ V) (hS7 : reg regS7 = treeM n + n)
    (hge : treeM n ≤ reg regLoopI) (hI : reg regLoopI < 2 * treeM n) :
    ∃ q₁ r1,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → r1 k = reg k) ∧
      r1 regEndU = (if reg regLoopI < treeM n + n then netV1 n + n + (reg regLoopI - treeM n)
                    else netV14 n + (reg regLoopI - (treeM n + n))) ∧
      RMExec rmB2Br3 V inp (Sum.inl 0) reg q₁ r1 [] (45 * n + 35) := by
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hn_M : n ≤ treeM n := le_treeM n
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hv15_le : netV15 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16]; omega
  have hN : reg regN = n := hp.1
  have hTM : reg regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hV1 : reg regV1 = netV1 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV14 : reg regV14 = netV14 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set leaf := reg regLoopI
  rcases rmCmpLt_spec regS0 regLoopI regS7 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
      V inp reg hreg h1V with ⟨r4, h4_fl, h4_fr, hcmp3⟩
  have h4_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV ∨ k = regS7 →
      r4 k = reg k := by
    intro k hk
    have hne : ∀ r : Fin EncR, r = regS0 ∨ r = regS1 ∨ r = regS2 → k ≠ r := by
      intro r hr heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
    exact h4_fr k (hne regS0 (Or.inl rfl)) (hne regS1 (Or.inr (Or.inl rfl))) (hne regS2 (Or.inr (Or.inr rfl)))
  have h4_I : r4 regLoopI = leaf := h4_keep regLoopI (Or.inr (Or.inl rfl))
  have h4_N : r4 regN = n := by rw [h4_keep regN (Or.inl (by decide)), hN]
  have h4_TM : r4 regTreeM = treeM n := by rw [h4_keep regTreeM (Or.inl (by decide)), hTM]
  have h4_S7 : r4 regS7 = treeM n + n := by rw [h4_keep regS7 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hS7]
  have h4_V1 : r4 regV1 = netV1 n := by rw [h4_keep regV1 (Or.inl (by decide)), hV1]
  have h4_V14 : r4 regV14 = netV14 n := by rw [h4_keep regV14 (Or.inl (by decide)), hV14]
  have hbr3 : ∃ q3 rB,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → rB k = r4 k) ∧
      rB regEndU = (if leaf < treeM n + n then netV1 n + n + (leaf - treeM n)
                    else netV14 n + (leaf - (treeM n + n))) ∧
      RMExec (rmIfZero regS0 rmB2Br3Else rmB2Br3Then (Sum.inl false) (Sum.inl false))
        V inp rmIfZeroEntry r4 q3 rB [] (30 * n + 25) := by
    by_cases hlt3 : leaf < treeM n + n
    · have hfl3 : r4 regS0 ≠ 0 := by rw [h4_fl, hS7]; simp [leaf, hlt3]
      have hc1 := rmCopy_spec regS1 regLoopI V inp r4 hcmp3.reg₁_le
      set t1 := regUpd r4 regS1 (r4 regLoopI)
      have hs2 := rmSub_spec regS1 regTreeM regS2 (by decide) V inp t1 hc1.reg₁_le
      set t2 := regUpd (regUpd t1 regS1 (t1 regS1 - t1 regTreeM)) regS2 0
      have ht2_S1 : t2 regS1 = leaf - treeM n := by simp [t2, t1, h4_I, h4_TM]
      have ha3 := rmSetAdd_spec regS3 regV1 regN (by decide) (by decide) (by decide)
        V inp t2 hs2.reg₁_le (by simp [t2, t1, h4_V1, h4_N, netV1]; omega)
      set t3 := regUpd (regUpd t2 regS3 (t2 regV1 + t2 regN)) regS0 0
      have ht3_S3 : t3 regS3 = netV1 n + n := by simp [t3, t2, t1, h4_V1, h4_N]
      have ht3_S1 : t3 regS1 = leaf - treeM n := by simp [t3, ht2_S1]
      have ha4 := rmSetAdd_spec regEndU regS3 regS1 (by decide) (by decide) (by decide)
        V inp t3 ha3.reg₁_le (by rw [ht3_S3, ht3_S1]; simp only [netV1]; omega)
      have hth := rmChain_spec_inl (by simp [rmCopy]) hc1
        (rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs2
          (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha3 ha4))
      have hT3 : 2 + (1 + (2 * t1 regTreeM + 2 + (2 * t2 regN + 3 + (2 * t3 regS1 + 3)))) ≤ 30 * n + 25 := by
        have ht1TM : t1 regTreeM = treeM n := by simp [t1, h4_TM]
        have ht2N : t2 regN = n := by simp [t2, t1, h4_N]
        rw [ht1TM, ht2N, ht3_S1]; omega
      have hif3 := (rmIfZero_pos_spec regS0 rmB2Br3Else (Sum.inl false) hfl3 hth).weaken
        (V₂ := V) (T₂ := 30 * n + 25) (by simp) hT3
      simp only [List.nil_append] at hif3
      refine ⟨_, _, ?_, by simp [hlt3, ht3_S3, ht3_S1], hif3⟩
      intro k hk
      have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU → k ≠ r := by
        intro r hr heq; have hv := congrArg Fin.val heq
        rcases hk with hk | rfl | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
      dsimp only [t3, t2, t1]
      rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr rfl)),
          regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS3 (Or.inl (by decide))),
          regUpd_ne _ (hne regS2 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
          regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
    · have hfl3 : r4 regS0 = 0 := by rw [h4_fl, hS7]; simp [leaf, hlt3]
      have hc1 := rmCopy_spec regS1 regLoopI V inp r4 hcmp3.reg₁_le
      set t1 := regUpd r4 regS1 (r4 regLoopI)
      have hs2 := rmSub_spec regS1 regS7 regS2 (by decide) V inp t1 hc1.reg₁_le
      set t2 := regUpd (regUpd t1 regS1 (t1 regS1 - t1 regS7)) regS2 0
      have ht2_S1 : t2 regS1 = leaf - (treeM n + n) := by simp [t2, t1, h4_I, h4_S7]
      have ht2_V14 : t2 regV14 = netV14 n := by simp [t2, t1, h4_V14]
      have ha3 := rmSetAdd_spec regEndU regV14 regS1 (by decide) (by decide) (by decide)
        V inp t2 hs2.reg₁_le (by
          rw [ht2_V14, ht2_S1]
          have : netV14 n + (treeM n - n) = netV15 n := rfl
          omega)
      have hel := rmChain_spec_inl (by simp [rmCopy]) hc1
        (rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs2 ha3)
      have hT3 : 2 + (1 + (2 * t1 regS7 + 2 + (2 * t2 regS1 + 3))) ≤ 30 * n + 25 := by
        have ht1S7 : t1 regS7 = treeM n + n := by simp [t1, h4_S7]
        rw [ht1S7, ht2_S1]; omega
      have hif3 := (rmIfZero_zero_spec regS0 rmB2Br3Then (Sum.inl false) hfl3 hel).weaken
        (V₂ := V) (T₂ := 30 * n + 25) (by simp) hT3
      simp only [List.nil_append] at hif3
      refine ⟨_, _, ?_, by simp [hlt3, ht2_V14, ht2_S1], hif3⟩
      intro k hk
      have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU → k ≠ r := by
        intro r hr heq; have hv := congrArg Fin.val heq
        rcases hk with hk | rfl | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
      dsimp only [t2, t1]
      rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr rfl)),
          regUpd_ne _ (hne regS2 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
          regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
  rcases hbr3 with ⟨q3, rB, hB_keep, hB_U, hif3⟩
  have hcomb := rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3 hif3
  have hT : 2 * min (reg regLoopI) (reg regS7) + 6 + (30 * n + 25) ≤ 45 * n + 35 := by
    rw [hS7]; have : min (reg regLoopI) (treeM n + n) ≤ treeM n + n := min_le_right _ _
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 45 * n + 35) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨_, rB, fun k hk => by
    rw [hB_keep k hk, h4_keep k (by rcases hk with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inl h))))],
    hB_U, hfin⟩

lemma rmB2Br2_spec (n V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ j, reg j ≤ V)
    (hV : 500 * n + 20 ≤ V) (hS7 : reg regS7 = treeM n + n)
    (hge : n ≤ reg regLoopI) (hI : reg regLoopI < 2 * treeM n) :
    ∃ q₁ r1,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → r1 k = reg k) ∧
      r1 regEndU = (if reg regLoopI < treeM n then netV13 n + (reg regLoopI - n)
                    else if reg regLoopI < treeM n + n then netV1 n + n + (reg regLoopI - treeM n)
                    else netV14 n + (reg regLoopI - (treeM n + n))) ∧
      RMExec rmB2Br2 V inp (Sum.inl 0) reg q₁ r1 [] (70 * n + 55) := by
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hv15_le : netV15 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16]; omega
  have hN : reg regN = n := hp.1
  have hTM : reg regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hV13 : reg regV13 = netV13 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set leaf := reg regLoopI
  rcases rmCmpLt_spec regS0 regLoopI regTreeM regS1 regS2 (by decide) (by decide) (by decide) (by decide)
      V inp reg hreg h1V with ⟨r3, h3_fl, h3_fr, hcmp2⟩
  have h3_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV ∨ k = regS7 →
      r3 k = reg k := by
    intro k hk
    have hne : ∀ r : Fin EncR, r = regS0 ∨ r = regS1 ∨ r = regS2 → k ≠ r := by
      intro r hr heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
    exact h3_fr k (hne regS0 (Or.inl rfl)) (hne regS1 (Or.inr (Or.inl rfl))) (hne regS2 (Or.inr (Or.inr rfl)))
  have h3_I : r3 regLoopI = leaf := h3_keep regLoopI (Or.inr (Or.inl rfl))
  have h3_N : r3 regN = n := by rw [h3_keep regN (Or.inl (by decide)), hN]
  have h3_S7 : r3 regS7 = treeM n + n := by rw [h3_keep regS7 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hS7]
  have h3_V13 : r3 regV13 = netV13 n := by rw [h3_keep regV13 (Or.inl (by decide)), hV13]
  have hbr2 : ∃ q2 rB,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → rB k = r3 k) ∧
      rB regEndU = (if leaf < treeM n then netV13 n + (leaf - n)
                    else if leaf < treeM n + n then netV1 n + n + (leaf - treeM n)
                    else netV14 n + (leaf - (treeM n + n))) ∧
      RMExec (rmIfZero regS0 rmB2Br3 rmB2Br2Then (Sum.inl 0) (Sum.inl false))
        V inp rmIfZeroEntry r3 q2 rB [] (50 * n + 40) := by
    by_cases hlt2 : leaf < treeM n
    · have hfl2 : r3 regS0 ≠ 0 := by rw [h3_fl, hTM]; simp [leaf, hlt2]
      have hc1 := rmCopy_spec regS1 regLoopI V inp r3 hcmp2.reg₁_le
      set t1 := regUpd r3 regS1 (r3 regLoopI)
      have hs2 := rmSub_spec regS1 regN regS2 (by decide) V inp t1 hc1.reg₁_le
      set t2 := regUpd (regUpd t1 regS1 (t1 regS1 - t1 regN)) regS2 0
      have ht2_S1 : t2 regS1 = leaf - n := by simp [t2, t1, h3_I, h3_N]
      have ht2_V13 : t2 regV13 = netV13 n := by simp [t2, t1, h3_V13]
      have ha3 := rmSetAdd_spec regEndU regV13 regS1 (by decide) (by decide) (by decide)
        V inp t2 hs2.reg₁_le (by
          rw [ht2_V13, ht2_S1]
          have : netV13 n + (treeM n - n) ≤ netV15 n := by simp only [netV15, netV14]; omega
          omega)
      have hth := rmChain_spec_inl (by simp [rmCopy]) hc1
        (rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs2 ha3)
      have hT2 : 2 + (1 + (2 * t1 regN + 2 + (2 * t2 regS1 + 3))) ≤ 50 * n + 40 := by
        have ht1N : t1 regN = n := by simp [t1, h3_N]
        rw [ht1N, ht2_S1]; omega
      have hif2 := (rmIfZero_pos_spec regS0 rmB2Br3 (Sum.inl 0) hfl2 hth).weaken
        (V₂ := V) (T₂ := 50 * n + 40) (by simp) hT2
      simp only [List.nil_append] at hif2
      refine ⟨_, _, ?_, by simp [hlt2, ht2_V13, ht2_S1], hif2⟩
      intro k hk
      have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU → k ≠ r := by
        intro r hr heq; have hv := congrArg Fin.val heq
        rcases hk with hk | rfl | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
      dsimp only [t2, t1]
      rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr rfl)),
          regUpd_ne _ (hne regS2 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
          regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
    · have hfl2 : r3 regS0 = 0 := by rw [h3_fl, hTM]; simp [leaf, hlt2]
      have hp3 := hp.of_preserved (fun k hk => h3_keep k (Or.inl hk))
      rcases rmB2Br3_spec n V inp r3 hn hp3 hcmp2.reg₁_le hV h3_S7
          (by rw [h3_I]; omega) (by rw [h3_I]; exact hI)
        with ⟨q3, rB, hB_keep, hB_U, hex3⟩
      have hif2 := (rmIfZero_zero_spec regS0 rmB2Br2Then (Sum.inl false) hfl2 hex3).weaken
        (V₂ := V) (T₂ := 50 * n + 40) (le_refl _) (by omega)
      refine ⟨_, rB, hB_keep, by rw [hB_U, h3_I]; simp [hlt2], hif2⟩
  rcases hbr2 with ⟨q2, rB, hB_keep, hB_U, hif2⟩
  have hcomb := rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp2 hif2
  have hT : 2 * min (reg regLoopI) (reg regTreeM) + 6 + (50 * n + 40) ≤ 70 * n + 55 := by
    rw [hTM]; have : min (reg regLoopI) (treeM n) ≤ treeM n := min_le_right _ _
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 70 * n + 55) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨_, rB, fun k hk => by
    rw [hB_keep k hk, h3_keep k (by rcases hk with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inl h))))],
    hB_U, hfin⟩

lemma rmB2Src_spec (n V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ j, reg j ≤ V)
    (hV : 500 * n + 20 ≤ V) (hI : reg regLoopI < 2 * treeM n) :
    ∃ q₁ r1,
      PreservedRegs r1 reg ∧
      r1 regLoopI = reg regLoopI ∧
      r1 regLoopRem = reg regLoopRem ∧
      r1 regEndV = reg regEndV ∧
      r1 regEndU = (endsB2 n (reg regLoopI)).1 ∧
      RMExec rmB2Src V inp rmB2SrcEntry reg q₁ r1 [] (100 * n + 80) := by
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hN : reg regN = n := hp.1
  have hTM : reg regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hV1 : reg regV1 = netV1 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set leaf := reg regLoopI
  have ha0 := rmSetAdd_spec regS7 regTreeM regN (by decide) (by decide) (by decide)
    V inp reg hreg (by rw [hTM, hN]; omega)
  set r1 := regUpd (regUpd reg regS7 (reg regTreeM + reg regN)) regS0 0
  have h1_S7 : r1 regS7 = treeM n + n := by simp [r1, hTM, hN]
  have h1_I : r1 regLoopI = leaf := by simp [r1, leaf]
  have h1_N : r1 regN = n := by simp [r1, hN]
  rcases rmCmpLt_spec regS0 regLoopI regN regS1 regS2 (by decide) (by decide) (by decide) (by decide)
      V inp r1 ha0.reg₁_le h1V with ⟨r2, h2_fl, h2_fr, hcmp1⟩
  have h2_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → r2 k = reg k := by
    intro k hk
    have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) → k ≠ r := by
      intro r hr heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl <;> (try simp at hv) <;> omega
    rw [h2_fr k (hne regS0 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide))]
    dsimp only [r1]
    rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS7 (by decide))]
  have h2_S7 : r2 regS7 = treeM n + n := by
    rw [h2_fr regS7 (by decide) (by decide) (by decide), h1_S7]
  have h2_I : r2 regLoopI = leaf := h2_keep regLoopI (Or.inr (Or.inl rfl))
  have h2_V1 : r2 regV1 = netV1 n := by rw [h2_keep regV1 (Or.inl (by decide)), hV1]
  have hbr1 : ∃ qB rB,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndV → rB k = r2 k) ∧
      rB regEndU = (endsB2 n leaf).1 ∧
      RMExec (rmIfZero regS0 rmB2Br2 (rmSetAdd regEndU regV1 regLoopI) (Sum.inl 0) rmSetAddEntry)
        V inp rmIfZeroEntry r2 qB rB [] (80 * n + 60) := by
    by_cases hlt1 : leaf < n
    · have hfl1 : r2 regS0 ≠ 0 := by rw [h2_fl, h1_I, h1_N]; simp [hlt1]
      have haU := rmSetAdd_spec regEndU regV1 regLoopI (by decide) (by decide) (by decide)
        V inp r2 hcmp1.reg₁_le (by rw [h2_V1, h2_I]; simp only [netV1]; omega)
      have hif1 := (rmIfZero_pos_spec regS0 rmB2Br2 (Sum.inl 0) hfl1 haU).weaken
        (V₂ := V) (T₂ := 80 * n + 60) (le_refl _) (by rw [h2_I]; omega)
      refine ⟨_, _, ?_, by simp [endsB2, hlt1, h2_V1, h2_I], hif1⟩
      intro k hk
      have hne : ∀ r : Fin EncR, r = regS0 ∨ r = regEndU → k ≠ r := by
        intro r hr heq; have hv := congrArg Fin.val heq
        rcases hk with hk | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> simp at hv ⊢ <;> omega
      rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndU (Or.inr rfl))]
    · have hfl1 : r2 regS0 = 0 := by rw [h2_fl, h1_I, h1_N]; simp [hlt1]
      have hp2 := hp.of_preserved (fun k hk => h2_keep k (Or.inl hk))
      rcases rmB2Br2_spec n V inp r2 hn hp2 hcmp1.reg₁_le hV h2_S7
          (by rw [h2_I]; omega) (by rw [h2_I]; exact hI)
        with ⟨q2, rB, hB_keep, hB_U, hex2⟩
      have hif1 := (rmIfZero_zero_spec regS0 (rmSetAdd regEndU regV1 regLoopI) rmSetAddEntry hfl1 hex2).weaken
        (V₂ := V) (T₂ := 80 * n + 60) (le_refl _) (by omega)
      refine ⟨_, rB, hB_keep, by rw [hB_U, h2_I]; simp [endsB2, hlt1], hif1⟩
  rcases hbr1 with ⟨qB, rB, hB_keep, hB_U, hif1⟩
  have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha0
    (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp1 hif1)
  have hT : 2 * reg regN + 3 + (2 * min (r1 regLoopI) (r1 regN) + 6 + (80 * n + 60)) ≤ 100 * n + 80 := by
    rw [hN, h1_I, h1_N]; have : min leaf n ≤ n := min_le_right _ _
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 100 * n + 80) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨_, rB, fun k hk => by rw [hB_keep k (Or.inl hk), h2_keep k (Or.inl hk)],
    by rw [hB_keep regLoopI (Or.inr (Or.inl rfl)), h2_I],
    by rw [hB_keep regLoopRem (Or.inr (Or.inr (Or.inl rfl))), h2_keep regLoopRem (Or.inr (Or.inr (Or.inl rfl)))],
    by rw [hB_keep regEndV (Or.inr (Or.inr (Or.inr rfl))), h2_keep regEndV (Or.inr (Or.inr (Or.inr rfl)))],
    hB_U, hfin⟩

lemma rmEmitB2_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB2 V inp rmEmitB2Entry reg₀ rmEmitB2Exit reg₁
        ((List.range (2 * treeM n)).flatMap (fun e => emitEdgeBits (endsB2 n e)))
        (10000 * n ^ 2 + 1000 * n + 20) := by
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hn_M : n ≤ treeM n := le_treeM n
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have ha0 := rmSetAdd_spec regLoopJ regTreeM regTreeM (by decide) (by decide) (by decide)
    V inp reg₀ hreg₀ (by rw [hTM]; omega)
  set r0 := regUpd (regUpd reg₀ regLoopJ (reg₀ regTreeM + reg₀ regTreeM)) regS0 0
  have hr0_pr : PreservedRegs r0 reg₀ :=
    (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (PreservedRegs.upd_ge _ regLoopJ _ (by decide))
  have hr0_cnt : r0 regLoopJ = 2 * treeM n := by simp [r0, hTM]; omega
  rcases rmEdgeLoop_spec regLoopJ (by decide) rmB2Body rmB2BodyEntry V (2200 * n + 220) inp r0
      (fun e => emitEdgeBits (endsB2 n e)) ha0.reg₁_le (by
        intro i reg hi hpr hreg hI
        have hp' := hp.of_preserved (hpr.trans hr0_pr)
        have hi' : i < 2 * treeM n := by omega
        rcases rmB2Dst_spec n V inp reg hn hp' hreg hV (by rw [hI]; exact hi')
          with ⟨r1, h1_pr, h1_I, h1_rem, h1_V, hd1⟩
        have hp1 := hp'.of_preserved h1_pr
        rcases rmB2Src_spec n V inp r1 hn hp1 hd1.reg₁_le hV (by rw [h1_I, hI]; exact hi')
          with ⟨q2, r2, h2_pr, h2_I, h2_rem, h2_V, h2_U, hs2⟩
        have he := rmEmitEndPair_spec V inp r2 hs2.reg₁_le
        have hact_dst : rmB2Dst rmB2DstEntry ≠ none := by
          simp [rmB2Dst, rmB2DstEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
        have hact_src : rmB2Src rmB2SrcEntry ≠ none := by
          simp [rmB2Src, rmB2SrcEntry, rmChain, rmSeq, rmSetAdd, rmSetAddEntry, rmCopy]
        have hcomb := rmChain_spec_inl hact_dst hd1 (rmChain_spec_inl hact_src hs2 he)
        have h2_U' : r2 regEndU = (endsB2 n i).1 := by rw [h2_U, h1_I, hI]
        have h2_V' : r2 regEndV = (endsB2 n i).2 := by rw [h2_V, h1_V, hI]; rfl
        have hU_le : r2 regEndU ≤ 500 * n + 20 := by
          rw [h2_U']; simp only [endsB2]
          have hv15_le : netV15 n ≤ netVertCount n := by
            simp only [netVertCount, netV18, netV17, netV16]; omega
          have hv14_eq : netV14 n = netV13 n + (treeM n - n) := rfl
          have hv15_eq : netV15 n = netV14 n + (treeM n - n) := rfl
          split_ifs <;> (try simp only [netV1]) <;> omega
        have hV_le : r2 regEndV ≤ 500 * n + 20 := by
          rw [h2_V']; simp only [endsB2]
          have h2M_vo := two_mul_treeM_le_treeVertOff n
          have hv16_le : netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ netVertCount n := by
            simp only [netVertCount, netV18, netV17, netV16]; omega
          omega
        have hT : 100 * n + 40 + (100 * n + 80 + (2 * r2 regEndU + 2 * r2 regEndV + 6)) ≤ 2200 * n + 220 := by
          omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2200 * n + 220) (by simp) hT
        simp only [List.nil_append, h2_U', h2_V', Prod.mk.eta] at hfin
        exact ⟨_, _, (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (h2_pr.trans h1_pr),
          by simp [h2_I, h1_I, hI], by simp [h2_rem, h1_rem], hfin⟩)
    with ⟨reg₁, hpr₁, hloop⟩
  rw [hr0_cnt] at hloop
  have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha0 hloop
  have hT : 2 * reg₀ regTreeM + 3 + (2 * treeM n * (2200 * n + 220 + 2) + 3) ≤ 10000 * n ^ 2 + 1000 * n + 20 := by
    rw [hTM]
    have hmul : 2 * treeM n * (2200 * n + 220 + 2) ≤ 4 * n * (2200 * n + 222) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 4 * n * (2200 * n + 222) = 8800 * n ^ 2 + 888 * n := by ring
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 10000 * n ^ 2 + 1000 * n + 20) (by simp) hT
  simp only [List.nil_append] at hfin
  exact ⟨reg₁, hpr₁.trans hr0_pr, hfin⟩

/-- Block B3 (`n` edges): `(netV2 n + idx, netV3 n + ((idx / J) % L2))`. -/
abbrev RMB3BodyQ : Type := RMSetAddQ ⊕ (RMDivModQ ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ RMEmitEndPairQ)))
abbrev RMEmitB3Q : Type := RMForRangeQ RMB3BodyQ

def rmB3Body : RMProg EncR RMB3BodyQ :=
  rmChain (rmSetAdd regEndU regV2 regLoopI)
    (rmChain (rmDivMod regS1 regS2 regLoopI regJ regS3 regS4 regS5)
      (rmChain (rmDivMod regS2 regS3 regS1 regL2 regS4 regS5 regS6)
        (rmChain (rmSetAdd regEndV regV3 regS3) rmEmitEndPair rmEmitEndPairEntry)
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmDivModEntry))
    (Sum.inl rmDivModEntry)

def rmB3BodyEntry : RMB3BodyQ := Sum.inl rmSetAddEntry

def rmEmitB3 : RMProg EncR RMEmitB3Q :=
  rmForRange regLoopI regLoopRem regN rmB3Body rmB3BodyEntry

lemma rmEmitB3_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB3 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range n).flatMap (fun e => emitEdgeBits (endsB3 n e)))
        (2500 * n ^ 2 + 300 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL2_pos : 0 < paramL2 n := one_le_paramL2 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) (paramL_le_27_mul hn)
  have hvc : netVertCount n ≤ 500 * n + 20 := netVertCount_le hn
  have hv4_le : netV3 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV3]; omega
  have hcnt : reg₀ regN = n := hp.1
  rcases rmEdgeLoop_spec regN (by decide) rmB3Body rmB3BodyEntry V (2200 * n + 200) inp reg₀
      (fun e => emitEdgeBits (endsB3 n e)) hreg₀ (by
        intro i reg hi hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hJ : reg regJ = paramJ n := hp'.2.2.1
        have hL2 : reg regL2 = paramL2 n := hp'.2.2.2.2.2.2.2.1
        have hV2 : reg regV2 = netV2 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV3 : reg regV3 = netV3 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hi' : i < n := by omega
        have haU := rmSetAdd_spec regEndU regV2 regLoopI (by decide) (by decide) (by decide)
          V inp reg hreg (by rw [hV2, hI]; simp only [netV2]; omega)
        set s1 := regUpd (regUpd reg regEndU (reg regV2 + reg regLoopI)) regS0 0
        have hs1_I : s1 regLoopI = i := by simp [s1, hI]
        have hs1_J : s1 regJ = paramJ n := by simp [s1, hJ]
        rcases rmDivMod_spec regS1 regS2 regLoopI regJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_J]; exact hJ_pos) haU.reg₁_le h1V
          with ⟨s2, hs2_q, _, hs2_fr, hd2⟩
        have hs2_q' : s2 regS1 = i / paramJ n := by rw [hs2_q, hs1_I, hs1_J]
        have hs2_L2 : s2 regL2 = paramL2 n := by
          rw [hs2_fr regL2 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hL2]
        rcases rmDivMod_spec regS2 regS3 regS1 regL2 regS4 regS5 regS6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s2 (by rw [hs2_L2]; exact hL2_pos) hd2.reg₁_le h1V
          with ⟨s3, _, hs3_r, hs3_fr, hd3⟩
        have hs3_r' : s3 regS3 = (i / paramJ n) % paramL2 n := by rw [hs3_r, hs2_q', hs2_L2]
        have hs3_V3 : s3 regV3 = netV3 n := by
          rw [hs3_fr regV3 (by decide) (by decide) (by decide) (by decide) (by decide),
              hs2_fr regV3 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hV3]
        have hmod_lt : (i / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2_pos
        have haV := rmSetAdd_spec regEndV regV3 regS3 (by decide) (by decide) (by decide)
          V inp s3 hd3.reg₁_le (by rw [hs3_V3, hs3_r']; omega)
        set s4 := regUpd (regUpd s3 regEndV (s3 regV3 + s3 regS3)) regS0 0
        have hs4_U : s4 regEndU = netV2 n + i := by
          dsimp only [s4]
          rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
              hs3_fr regEndU (by decide) (by decide) (by decide) (by decide) (by decide),
              hs2_fr regEndU (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s1, hV2, hI]
        have hs4_V : s4 regEndV = netV3 n + (i / paramJ n) % paramL2 n := by
          simp [s4, hs3_V3, hs3_r']
        have he := rmEmitEndPair_spec V inp s4 haV.reg₁_le
        have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
          intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
        have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) haU
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd2
            (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd3
              (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) haV he)))
        have hdiv_le : i / paramJ n ≤ n := le_trans (Nat.div_le_self _ _) (by omega)
        have hT : 2 * reg regLoopI + 3 + (15 * s1 regLoopI + 2 * s1 regJ + 10 +
            (15 * s2 regS1 + 2 * s2 regL2 + 10 + (2 * s3 regS3 + 3 + (2 * s4 regEndU + 2 * s4 regEndV + 6)))) ≤
            2200 * n + 200 := by
          rw [hI, hs1_I, hs1_J, hs2_q', hs2_L2, hs3_r', hs4_U, hs4_V]
          simp only [netV2]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2200 * n + 200) (by simp) hT
        simp only [List.nil_append, hs4_U, hs4_V] at hfin
        have hkeep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem →
            regUpd s4 regS0 0 k = reg k := by
          intro k hk
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU ∨ r = regEndV → k ≠ r := by
            intro r hr heq
            have hv := congrArg Fin.val heq
            rcases hk with hk | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
          dsimp only [s4]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
              regUpd_ne _ (hne regEndV (Or.inr (Or.inr rfl))),
              hs3_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
                (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))),
              hs2_fr k (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
          dsimp only [s1]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl)))]
        exact ⟨_, _, fun k hk => hkeep k (Or.inl hk),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : n * (2200 * n + 200 + 2) + 3 ≤ 2500 * n ^ 2 + 300 * n + 10 := by
    have : n * (2200 * n + 200 + 2) + 3 = 2200 * n ^ 2 + 202 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 2500 * n ^ 2 + 300 * n + 10) (le_refl _) hT⟩

/-! ### Edge Block Emitters B4, B5, B6, B7, B8, B9, B10, B11 -/

/-- Shared loop for Blocks B4 (`V3, V4`), B6 (`V5, V6`), B9 (`V8, V9`):
for `k < 2 * J * L`, `rem := k / (2 * J)`, emits `(baseU + rem / L1, baseV + rem % L1)`. -/
abbrev RMDivModPairBodyQ : Type :=
  RMDivModQ ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ (RMSetAddQ ⊕ RMEmitEndPairQ)))
abbrev RMEmitDivModPairQ : Type := RMForRangeQ RMDivModPairBodyQ

def rmDivModPairBody (rBaseU rBaseV : Fin EncR) : RMProg EncR RMDivModPairBodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5)
    (rmChain (rmDivMod regS2 regS3 regS1 regL1 regS4 regS5 regS6)
      (rmChain (rmSetAdd regEndU rBaseU regS2)
        (rmChain (rmSetAdd regEndV rBaseV regS3) rmEmitEndPair rmEmitEndPairEntry)
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmDivModPairBodyEntry : RMDivModPairBodyQ := Sum.inl rmDivModEntry

def rmEmitDivModPairLoop (rBaseU rBaseV : Fin EncR) : RMProg EncR RMEmitDivModPairQ :=
  rmForRange regLoopI regLoopRem regTwoJL (rmDivModPairBody rBaseU rBaseV) rmDivModPairBodyEntry

lemma rmEmitDivModPairLoop_spec (rBaseU rBaseV : Fin EncR)
    (hrU : rBaseU.val < 41) (hrV : rBaseV.val < 41)
    (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hU_bd : reg₀ rBaseU + paramL2 n ≤ 500 * n + 20)
    (hV_bd : reg₀ rBaseV + paramL1 n ≤ 500 * n + 20) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec (rmEmitDivModPairLoop rBaseU rBaseV) V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun k =>
          let rem := k / (2 * paramJ n)
          emitEdgeBits (reg₀ rBaseU + rem / paramL1 n, reg₀ rBaseV + rem % paramL1 n)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL1_pos : 0 < paramL1 n := one_le_paramL1 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hL1_le : paramL1 n ≤ 27 * n := le_trans (paramL1_le_paramL n) hL_le
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) hL_le
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  have hL_prod : paramL1 n * paramL2 n = paramL n := paramL1_mul_paramL2 n
  have hcnt : reg₀ regTwoJL = 2 * paramJ n * paramL n :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases rmEdgeLoop_spec regTwoJL (by decide) (rmDivModPairBody rBaseU rBaseV) rmDivModPairBodyEntry
      V (3500 * n + 200) inp reg₀
      (fun k =>
        let rem := k / (2 * paramJ n)
        emitEdgeBits (reg₀ rBaseU + rem / paramL1 n, reg₀ rBaseV + rem % paramL1 n))
      hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have h2J : reg regTwoJ = 2 * paramJ n :=
          hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hL1 : reg regL1 = paramL1 n := hp'.2.2.2.2.2.2.1
        have hBU : reg rBaseU = reg₀ rBaseU := hpr rBaseU hrU
        have hBV : reg rBaseV = reg₀ rBaseV := hpr rBaseV hrV
        have hk' : k < 2 * paramJ n * paramL n := by omega
        have hrem_lt : k / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul hk'
        have hdiv_lt : (k / (2 * paramJ n)) / paramL1 n < paramL2 n :=
          Nat.div_lt_of_lt_mul (by rw [hL_prod]; exact hrem_lt)
        have hmod_lt : (k / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1_pos
        rcases rmDivMod_spec regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [h2J]; omega) hreg h1V
          with ⟨s1, hs1_q, _, hs1_fr, hd1⟩
        have hs1_q' : s1 regS1 = k / (2 * paramJ n) := by rw [hs1_q, hI, h2J]
        have hs1_L1 : s1 regL1 = paramL1 n := by
          rw [hs1_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
        rcases rmDivMod_spec regS2 regS3 regS1 regL1 regS4 regS5 regS6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_L1]; exact hL1_pos) hd1.reg₁_le h1V
          with ⟨s2, hs2_q, hs2_r, hs2_fr, hd2⟩
        have hs2_q' : s2 regS2 = (k / (2 * paramJ n)) / paramL1 n := by rw [hs2_q, hs1_q', hs1_L1]
        have hs2_r' : s2 regS3 = (k / (2 * paramJ n)) % paramL1 n := by rw [hs2_r, hs1_q', hs1_L1]
        have hs2_pr : PreservedRegs s2 reg := fun j hj => by
          have hne : ∀ r : Fin EncR, 41 ≤ r.val → j ≠ r := fun r hr heq => by
            have := congrArg Fin.val heq; omega
          rw [hs2_fr j (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
                (hne regS5 (by decide)) (hne regS6 (by decide)),
              hs1_fr j (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        have hs2_BU : s2 rBaseU = reg₀ rBaseU := by rw [hs2_pr rBaseU hrU, hBU]
        have hs2_BV : s2 rBaseV = reg₀ rBaseV := by rw [hs2_pr rBaseV hrV, hBV]
        have haU := rmSetAdd_spec regEndU rBaseU regS2 (by decide) (by decide) (by decide)
          V inp s2 hd2.reg₁_le (by rw [hs2_BU, hs2_q']; omega)
        set s3 := regUpd (regUpd s2 regEndU (s2 rBaseU + s2 regS2)) regS0 0
        have hs3_BV : s3 rBaseV = reg₀ rBaseV := by
          dsimp only [s3]
          rw [regUpd_fin_ne _ _ _ _ (by simp; omega), regUpd_fin_ne _ _ _ _ (by simp; omega), hs2_BV]
        have hs3_S3 : s3 regS3 = (k / (2 * paramJ n)) % paramL1 n := by simp [s3, hs2_r']
        have haV := rmSetAdd_spec regEndV rBaseV regS3 (by decide) (by decide) (by decide)
          V inp s3 haU.reg₁_le (by rw [hs3_BV, hs3_S3]; omega)
        set s4 := regUpd (regUpd s3 regEndV (s3 rBaseV + s3 regS3)) regS0 0
        have hs4_U : s4 regEndU = reg₀ rBaseU + (k / (2 * paramJ n)) / paramL1 n := by
          simp [s4, s3, hs2_BU, hs2_q']
        have hs4_V : s4 regEndV = reg₀ rBaseV + (k / (2 * paramJ n)) % paramL1 n := by
          simp [s4, hs3_BV, hs3_S3]
        have he := rmEmitEndPair_spec V inp s4 haV.reg₁_le
        have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
          intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
        have hact_sa : ∀ a b c : Fin EncR, rmSetAdd a b c rmSetAddEntry ≠ none := by
          intros; simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
        have hcomb := rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd1
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd2
            (rmChain_spec_inl (hact_sa _ _ _) haU
              (rmChain_spec_inl (hact_sa _ _ _) haV he)))
        have hT : 15 * reg regLoopI + 2 * reg regTwoJ + 10 +
            (15 * s1 regS1 + 2 * s1 regL1 + 10 +
              (2 * s2 regS2 + 3 + (2 * s3 regS3 + 3 + (2 * s4 regEndU + 2 * s4 regEndV + 6)))) ≤
            3500 * n + 200 := by
          rw [hI, h2J, hs1_q', hs1_L1, hs2_q', hs3_S3, hs4_U, hs4_V]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 3500 * n + 200) (by simp) hT
        simp only [List.nil_append, hs4_U, hs4_V] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem →
            regUpd s4 regS0 0 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU ∨ r = regEndV → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
          dsimp only [s4, s3]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
              regUpd_ne _ (hne regEndV (Or.inr (Or.inr rfl))),
              regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl))),
              hs2_fr j (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
                (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))),
              hs1_fr j (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
        exact ⟨_, _, fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) + 3 ≤ 200000 * n ^ 2 + 12000 * n + 10 := by
    have hmul : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) ≤ 54 * n * (3500 * n + 200 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 54 * n * (3500 * n + 200 + 2) = 189000 * n ^ 2 + 10908 * n := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 200000 * n ^ 2 + 12000 * n + 10) (le_refl _) hT⟩

def rmEmitB4 : RMProg EncR RMEmitDivModPairQ := rmEmitDivModPairLoop regV3 regV4
def rmEmitB6 : RMProg EncR RMEmitDivModPairQ := rmEmitDivModPairLoop regV5 regV6
def rmEmitB9 : RMProg EncR RMEmitDivModPairQ := rmEmitDivModPairLoop regV8 regV9

lemma rmEmitB4_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB4 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB4 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have hvc := netVertCount_le hn
  have hV3 : reg₀ regV3 = netV3 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV4 : reg₀ regV4 = netV4 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h3_bd : netV3 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV3]; omega
  have h4_bd : netV4 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV4]; omega
  simpa [rmEmitB4, endsB4, hV3, hV4] using
    rmEmitDivModPairLoop_spec regV3 regV4 (by decide) (by decide) n V inp reg₀ hn hp hreg₀ hV
      (by rw [hV3]; omega) (by rw [hV4]; omega)

lemma rmEmitB6_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB6 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB6 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have hvc := netVertCount_le hn
  have hV5 : reg₀ regV5 = netV5 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV6 : reg₀ regV6 = netV6 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h5_bd : netV5 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV5]; omega
  have h6_bd : netV6 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV6]; omega
  simpa [rmEmitB6, endsB6, hV5, hV6] using
    rmEmitDivModPairLoop_spec regV5 regV6 (by decide) (by decide) n V inp reg₀ hn hp hreg₀ hV
      (by rw [hV5]; omega) (by rw [hV6]; omega)

lemma rmEmitB9_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB9 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB9 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have hvc := netVertCount_le hn
  have hV8 : reg₀ regV8 = netV8 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV9 : reg₀ regV9 = netV9 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h8_bd : netV8 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9]; omega
  have h9_bd : netV9 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10]; omega
  simpa [rmEmitB9, endsB9, hV8, hV9] using
    rmEmitDivModPairLoop_spec regV8 regV9 (by decide) (by decide) n V inp reg₀ hn hp hreg₀ hV
      (by rw [hV8]; omega) (by rw [hV9]; omega)

/-- Shared loop for Blocks B5 (`V4`) and B7 (`V6`):
for `k < 2 * J * L`, `q := k / (2 * J)`, emits `(baseU + q % L1, netV7 n + q)`. -/
def rmModDirectBody (rBaseU : Fin EncR) : RMProg EncR RMDivModPairBodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5)
    (rmChain (rmDivMod regS2 regS3 regS1 regL1 regS4 regS5 regS6)
      (rmChain (rmSetAdd regEndU rBaseU regS3)
        (rmChain (rmSetAdd regEndV regV7 regS1) rmEmitEndPair rmEmitEndPairEntry)
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmEmitModDirectLoop (rBaseU : Fin EncR) : RMProg EncR RMEmitDivModPairQ :=
  rmForRange regLoopI regLoopRem regTwoJL (rmModDirectBody rBaseU) rmDivModPairBodyEntry

lemma rmEmitModDirectLoop_spec (rBaseU : Fin EncR) (hrU : rBaseU.val < 41)
    (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hU_bd : reg₀ rBaseU + paramL1 n ≤ 500 * n + 20) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec (rmEmitModDirectLoop rBaseU) V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun k =>
          let q := k / (2 * paramJ n)
          emitEdgeBits (reg₀ rBaseU + q % paramL1 n, netV7 n + q)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL1_pos : 0 < paramL1 n := one_le_paramL1 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hL1_le : paramL1 n ≤ 27 * n := le_trans (paramL1_le_paramL n) hL_le
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  have hvc := netVertCount_le hn
  have hv8_le : netV7 n + paramL n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8]; omega
  have hcnt : reg₀ regTwoJL = 2 * paramJ n * paramL n :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases rmEdgeLoop_spec regTwoJL (by decide) (rmModDirectBody rBaseU) rmDivModPairBodyEntry
      V (3500 * n + 200) inp reg₀
      (fun k =>
        let q := k / (2 * paramJ n)
        emitEdgeBits (reg₀ rBaseU + q % paramL1 n, netV7 n + q))
      hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have h2J : reg regTwoJ = 2 * paramJ n :=
          hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hL1 : reg regL1 = paramL1 n := hp'.2.2.2.2.2.2.1
        have hV7 : reg regV7 = netV7 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hBU : reg rBaseU = reg₀ rBaseU := hpr rBaseU hrU
        have hk' : k < 2 * paramJ n * paramL n := by omega
        have hq_lt : k / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul hk'
        have hmod_lt : (k / (2 * paramJ n)) % paramL1 n < paramL1 n := Nat.mod_lt _ hL1_pos
        rcases rmDivMod_spec regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [h2J]; omega) hreg h1V
          with ⟨s1, hs1_q, _, hs1_fr, hd1⟩
        have hs1_q' : s1 regS1 = k / (2 * paramJ n) := by rw [hs1_q, hI, h2J]
        have hs1_L1 : s1 regL1 = paramL1 n := by
          rw [hs1_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
        rcases rmDivMod_spec regS2 regS3 regS1 regL1 regS4 regS5 regS6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_L1]; exact hL1_pos) hd1.reg₁_le h1V
          with ⟨s2, _, hs2_r, hs2_fr, hd2⟩
        have hs2_q' : s2 regS1 = k / (2 * paramJ n) := by
          rw [hs2_fr regS1 (by decide) (by decide) (by decide) (by decide) (by decide), hs1_q']
        have hs2_r' : s2 regS3 = (k / (2 * paramJ n)) % paramL1 n := by rw [hs2_r, hs1_q', hs1_L1]
        have hs2_pr : PreservedRegs s2 reg := fun j hj => by
          have hne : ∀ r : Fin EncR, 41 ≤ r.val → j ≠ r := fun r hr heq => by
            have := congrArg Fin.val heq; omega
          rw [hs2_fr j (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
                (hne regS5 (by decide)) (hne regS6 (by decide)),
              hs1_fr j (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        have hs2_BU : s2 rBaseU = reg₀ rBaseU := by rw [hs2_pr rBaseU hrU, hBU]
        have hs2_V7 : s2 regV7 = netV7 n := by rw [hs2_pr regV7 (by decide), hV7]
        have haU := rmSetAdd_spec regEndU rBaseU regS3 (by decide) (by decide) (by decide)
          V inp s2 hd2.reg₁_le (by rw [hs2_BU, hs2_r']; omega)
        set s3 := regUpd (regUpd s2 regEndU (s2 rBaseU + s2 regS3)) regS0 0
        have hs3_V7 : s3 regV7 = netV7 n := by simp [s3, hs2_V7]
        have hs3_S1 : s3 regS1 = k / (2 * paramJ n) := by simp [s3, hs2_q']
        have haV := rmSetAdd_spec regEndV regV7 regS1 (by decide) (by decide) (by decide)
          V inp s3 haU.reg₁_le (by rw [hs3_V7, hs3_S1]; omega)
        set s4 := regUpd (regUpd s3 regEndV (s3 regV7 + s3 regS1)) regS0 0
        have hs4_U : s4 regEndU = reg₀ rBaseU + (k / (2 * paramJ n)) % paramL1 n := by
          simp [s4, s3, hs2_BU, hs2_r']
        have hs4_V : s4 regEndV = netV7 n + k / (2 * paramJ n) := by
          simp [s4, hs3_V7, hs3_S1]
        have he := rmEmitEndPair_spec V inp s4 haV.reg₁_le
        have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
          intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
        have hact_sa : ∀ a b c : Fin EncR, rmSetAdd a b c rmSetAddEntry ≠ none := by
          intros; simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
        have hcomb := rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd1
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd2
            (rmChain_spec_inl (hact_sa _ _ _) haU
              (rmChain_spec_inl (hact_sa _ _ _) haV he)))
        have hT : 15 * reg regLoopI + 2 * reg regTwoJ + 10 +
            (15 * s1 regS1 + 2 * s1 regL1 + 10 +
              (2 * s2 regS3 + 3 + (2 * s3 regS1 + 3 + (2 * s4 regEndU + 2 * s4 regEndV + 6)))) ≤
            3500 * n + 200 := by
          rw [hI, h2J, hs1_q', hs1_L1, hs2_r', hs3_S1, hs4_U, hs4_V]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 3500 * n + 200) (by simp) hT
        simp only [List.nil_append, hs4_U, hs4_V] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem →
            regUpd s4 regS0 0 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU ∨ r = regEndV → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
          dsimp only [s4, s3]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
              regUpd_ne _ (hne regEndV (Or.inr (Or.inr rfl))),
              regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl))),
              hs2_fr j (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
                (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))),
              hs1_fr j (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
        exact ⟨_, _, fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) + 3 ≤ 200000 * n ^ 2 + 12000 * n + 10 := by
    have hmul : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) ≤ 54 * n * (3500 * n + 200 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 54 * n * (3500 * n + 200 + 2) = 189000 * n ^ 2 + 10908 * n := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 200000 * n ^ 2 + 12000 * n + 10) (le_refl _) hT⟩

def rmEmitB5 : RMProg EncR RMEmitDivModPairQ := rmEmitModDirectLoop regV4
def rmEmitB7 : RMProg EncR RMEmitDivModPairQ := rmEmitModDirectLoop regV6

lemma rmEmitB5_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB5 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB5 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have hvc := netVertCount_le hn
  have hV4 : reg₀ regV4 = netV4 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h4_bd : netV4 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV4]; omega
  simpa [rmEmitB5, endsB5, hV4] using
    rmEmitModDirectLoop_spec regV4 (by decide) n V inp reg₀ hn hp hreg₀ hV (by rw [hV4]; omega)

lemma rmEmitB7_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB7 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB7 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have hvc := netVertCount_le hn
  have hV6 : reg₀ regV6 = netV6 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h6_bd : netV6 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8, netV7, netV6]; omega
  simpa [rmEmitB7, endsB7, hV6] using
    rmEmitModDirectLoop_spec regV6 (by decide) n V inp reg₀ hn hp hreg₀ hV (by rw [hV6]; omega)

/-- Block B8 (`2 * J * L` edges): `(netV7 n + q, netV8 n + q % L2)`. -/
def rmB8Body : RMProg EncR RMDivModPairBodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5)
    (rmChain (rmDivMod regS2 regS3 regS1 regL2 regS4 regS5 regS6)
      (rmChain (rmSetAdd regEndU regV7 regS1)
        (rmChain (rmSetAdd regEndV regV8 regS3) rmEmitEndPair rmEmitEndPairEntry)
        (Sum.inl rmSetAddEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmEmitB8 : RMProg EncR RMEmitDivModPairQ :=
  rmForRange regLoopI regLoopRem regTwoJL rmB8Body rmDivModPairBodyEntry

lemma rmEmitB8_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB8 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB8 n e)))
        (200000 * n ^ 2 + 12000 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL2_pos : 0 < paramL2 n := one_le_paramL2 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hL2_le : paramL2 n ≤ 27 * n := le_trans (paramL2_le_paramL n) hL_le
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  have hvc := netVertCount_le hn
  have hv8_le : netV7 n + paramL n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9, netV8]; omega
  have hv9_le : netV8 n + paramL2 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11,
      netV10, netV9]; omega
  have hcnt : reg₀ regTwoJL = 2 * paramJ n * paramL n :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases rmEdgeLoop_spec regTwoJL (by decide) rmB8Body rmDivModPairBodyEntry
      V (3500 * n + 200) inp reg₀ (fun e => emitEdgeBits (endsB8 n e)) hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have h2J : reg regTwoJ = 2 * paramJ n :=
          hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hL2 : reg regL2 = paramL2 n := hp'.2.2.2.2.2.2.2.1
        have hV7 : reg regV7 = netV7 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV8 : reg regV8 = netV8 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hk' : k < 2 * paramJ n * paramL n := by omega
        have hq_lt : k / (2 * paramJ n) < paramL n := Nat.div_lt_of_lt_mul hk'
        have hmod_lt : (k / (2 * paramJ n)) % paramL2 n < paramL2 n := Nat.mod_lt _ hL2_pos
        rcases rmDivMod_spec regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [h2J]; omega) hreg h1V
          with ⟨s1, hs1_q, _, hs1_fr, hd1⟩
        have hs1_q' : s1 regS1 = k / (2 * paramJ n) := by rw [hs1_q, hI, h2J]
        have hs1_L2 : s1 regL2 = paramL2 n := by
          rw [hs1_fr regL2 (by decide) (by decide) (by decide) (by decide) (by decide), hL2]
        rcases rmDivMod_spec regS2 regS3 regS1 regL2 regS4 regS5 regS6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_L2]; exact hL2_pos) hd1.reg₁_le h1V
          with ⟨s2, _, hs2_r, hs2_fr, hd2⟩
        have hs2_q' : s2 regS1 = k / (2 * paramJ n) := by
          rw [hs2_fr regS1 (by decide) (by decide) (by decide) (by decide) (by decide), hs1_q']
        have hs2_r' : s2 regS3 = (k / (2 * paramJ n)) % paramL2 n := by rw [hs2_r, hs1_q', hs1_L2]
        have hs2_pr : PreservedRegs s2 reg := fun j hj => by
          have hne : ∀ r : Fin EncR, 41 ≤ r.val → j ≠ r := fun r hr heq => by
            have := congrArg Fin.val heq; omega
          rw [hs2_fr j (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
                (hne regS5 (by decide)) (hne regS6 (by decide)),
              hs1_fr j (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        have hs2_V7 : s2 regV7 = netV7 n := by rw [hs2_pr regV7 (by decide), hV7]
        have hs2_V8 : s2 regV8 = netV8 n := by rw [hs2_pr regV8 (by decide), hV8]
        have haU := rmSetAdd_spec regEndU regV7 regS1 (by decide) (by decide) (by decide)
          V inp s2 hd2.reg₁_le (by rw [hs2_V7, hs2_q']; omega)
        set s3 := regUpd (regUpd s2 regEndU (s2 regV7 + s2 regS1)) regS0 0
        have hs3_V8 : s3 regV8 = netV8 n := by simp [s3, hs2_V8]
        have hs3_S3 : s3 regS3 = (k / (2 * paramJ n)) % paramL2 n := by simp [s3, hs2_r']
        have haV := rmSetAdd_spec regEndV regV8 regS3 (by decide) (by decide) (by decide)
          V inp s3 haU.reg₁_le (by rw [hs3_V8, hs3_S3]; omega)
        set s4 := regUpd (regUpd s3 regEndV (s3 regV8 + s3 regS3)) regS0 0
        have hs4_U : s4 regEndU = netV7 n + k / (2 * paramJ n) := by simp [s4, s3, hs2_V7, hs2_q']
        have hs4_V : s4 regEndV = netV8 n + (k / (2 * paramJ n)) % paramL2 n := by simp [s4, hs3_V8, hs3_S3]
        have he := rmEmitEndPair_spec V inp s4 haV.reg₁_le
        have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
          intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
        have hact_sa : ∀ a b c : Fin EncR, rmSetAdd a b c rmSetAddEntry ≠ none := by
          intros; simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
        have hcomb := rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd1
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd2
            (rmChain_spec_inl (hact_sa _ _ _) haU
              (rmChain_spec_inl (hact_sa _ _ _) haV he)))
        have hT : 15 * reg regLoopI + 2 * reg regTwoJ + 10 +
            (15 * s1 regS1 + 2 * s1 regL2 + 10 +
              (2 * s2 regS1 + 3 + (2 * s3 regS3 + 3 + (2 * s4 regEndU + 2 * s4 regEndV + 6)))) ≤
            3500 * n + 200 := by
          rw [hI, h2J, hs1_q', hs1_L2, hs2_q', hs3_S3, hs4_U, hs4_V]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 3500 * n + 200) (by simp) hT
        simp only [List.nil_append, hs4_U, hs4_V] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem →
            regUpd s4 regS0 0 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU ∨ r = regEndV → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
          dsimp only [s4, s3]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
              regUpd_ne _ (hne regEndV (Or.inr (Or.inr rfl))),
              regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl))),
              hs2_fr j (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
                (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))),
              hs1_fr j (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
        exact ⟨_, _, fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) + 3 ≤ 200000 * n ^ 2 + 12000 * n + 10 := by
    have hmul : 2 * paramJ n * paramL n * (3500 * n + 200 + 2) ≤ 54 * n * (3500 * n + 200 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 54 * n * (3500 * n + 200 + 2) = 189000 * n ^ 2 + 10908 * n := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 200000 * n ^ 2 + 12000 * n + 10) (le_refl _) hT⟩

/-- Block B10 (`2 * J * L` edges): overlap-add output routing `endsB10`
(using `ovlTargetBit J blk p = blk * J + p`). -/
abbrev RMB10IfQ : Type := Option Bool ⊕ (RMSetAddQ ⊕ (Bool ⊕ RMSetAddQ))
abbrev RMB10BodyQ : Type :=
  RMDivModQ ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ (RMMulQ ⊕ (RMAddQ ⊕ (Fin 8 ⊕ (RMB10IfQ ⊕ RMEmitEndPairQ))))))
abbrev RMEmitB10Q : Type := RMForRangeQ RMB10BodyQ

def rmB10Body : RMProg EncR RMB10BodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5)
    (rmChain (rmDivMod regS3 regS4 regS1 regL1 regS5 regS6 regS7)
      (rmChain (rmSetAdd regEndU regV9 regS4)
        (rmChain (rmMul regS3 regS1 regJ regS4 regS5)
          (rmChain (rmAdd regS3 regS2 regS4)
            (rmChain (rmCmpLt regS0 regS3 regV1 regS4 regS5)
              (rmChain (rmIfZero regS0 (rmSetAdd regEndV regV10 regLoopI) (rmSetAdd regEndV regV11 regS3)
                  rmSetAddEntry rmSetAddEntry)
                rmEmitEndPair rmEmitEndPairEntry)
              (Sum.inl rmIfZeroEntry))
            (Sum.inl 0))
          (Sum.inl rmAddEntry))
        (Sum.inl rmMulEntry))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmB10BodyEntry : RMB10BodyQ := Sum.inl rmDivModEntry

def rmEmitB10 : RMProg EncR RMEmitB10Q :=
  rmForRange regLoopI regLoopRem regTwoJL rmB10Body rmB10BodyEntry

lemma rmEmitB10_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB10 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB10 n e)))
        (250000 * n ^ 2 + 15000 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hL_pos : 0 < paramL n := one_le_paramL n
  have hL1_pos : 0 < paramL1 n := one_le_paramL1 n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hL1_le : paramL1 n ≤ 27 * n := le_trans (paramL1_le_paramL n) hL_le
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  have hvc := netVertCount_le hn
  have hv10_le : netV9 n + paramL1 n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11, netV10]; omega
  have hv11_le : netV10 n + 2 * paramJ n * paramL n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12, netV11]; omega
  have hv12_le : netV11 n + 2 * n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12]; omega
  have hcnt : reg₀ regTwoJL = 2 * paramJ n * paramL n :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases rmEdgeLoop_spec regTwoJL (by decide) rmB10Body rmB10BodyEntry
      V (4000 * n + 220) inp reg₀ (fun e => emitEdgeBits (endsB10 n e)) hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hJ : reg regJ = paramJ n := hp'.2.2.1
        have hL1 : reg regL1 = paramL1 n := hp'.2.2.2.2.2.2.1
        have hV1 : reg regV1 = netV1 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV9 : reg regV9 = netV9 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV10 : reg regV10 = netV10 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV11 : reg regV11 = netV11 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h2J : reg regTwoJ = 2 * paramJ n :=
          hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hk' : k < 2 * paramJ n * paramL n := by omega
        set blk := k / (2 * paramJ n)
        set p := k % (2 * paramJ n)
        have hblk_lt : blk < paramL n := Nat.div_lt_of_lt_mul hk'
        have hp_lt : p < 2 * paramJ n := Nat.mod_lt _ (by omega)
        have hmod_lt : blk % paramL1 n < paramL1 n := Nat.mod_lt _ hL1_pos
        have hblkJ_lt : blk * paramJ n < 27 * n := by
          have h1 : blk * paramJ n ≤ paramL n * paramJ n := Nat.mul_le_mul_right _ (le_of_lt hblk_lt)
          have h2 : paramL n * paramJ n = paramJ n * paramL n := Nat.mul_comm _ _
          have h3 : 2 * paramJ n * paramL n = 2 * (paramJ n * paramL n) := by ring
          omega
        have htk_lt : blk * paramJ n + p < 54 * n := by omega
        rcases rmDivMod_spec regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [h2J]; omega) hreg h1V
          with ⟨s1, hs1_q, hs1_r, hs1_fr, hd1⟩
        have hs1_blk : s1 regS1 = blk := by rw [hs1_q, hI, h2J]
        have hs1_p : s1 regS2 = p := by rw [hs1_r, hI, h2J]
        have hs1_L1 : s1 regL1 = paramL1 n := by
          rw [hs1_fr regL1 (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
        rcases rmDivMod_spec regS3 regS4 regS1 regL1 regS5 regS6 regS7
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_L1]; exact hL1_pos) hd1.reg₁_le h1V
          with ⟨s2, _, hs2_r, hs2_fr, hd2⟩
        have hs2_r' : s2 regS4 = blk % paramL1 n := by rw [hs2_r, hs1_blk, hs1_L1]
        have hs2_blk : s2 regS1 = blk := by
          rw [hs2_fr regS1 (by decide) (by decide) (by decide) (by decide) (by decide), hs1_blk]
        have hs2_p : s2 regS2 = p := by
          rw [hs2_fr regS2 (by decide) (by decide) (by decide) (by decide) (by decide), hs1_p]
        have hs2_pr : PreservedRegs s2 reg := fun j hj => by
          have hne : ∀ r : Fin EncR, 41 ≤ r.val → j ≠ r := fun r hr heq => by
            have := congrArg Fin.val heq; omega
          rw [hs2_fr j (hne regS3 (by decide)) (hne regS4 (by decide)) (hne regS5 (by decide))
                (hne regS6 (by decide)) (hne regS7 (by decide)),
              hs1_fr j (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        have hs2_V9 : s2 regV9 = netV9 n := by rw [hs2_pr regV9 (by decide), hV9]
        have haU := rmSetAdd_spec regEndU regV9 regS4 (by decide) (by decide) (by decide)
          V inp s2 hd2.reg₁_le (by rw [hs2_V9, hs2_r']; omega)
        set s3 := regUpd (regUpd s2 regEndU (s2 regV9 + s2 regS4)) regS0 0
        have hs3_blk : s3 regS1 = blk := by simp [s3, hs2_blk]
        have hs3_p : s3 regS2 = p := by simp [s3, hs2_p]
        have hs3_J : s3 regJ = paramJ n := by simp [s3, hs2_pr regJ (by decide), hJ]
        have hs3_U : s3 regEndU = netV9 n + blk % paramL1 n := by simp [s3, hs2_V9, hs2_r']
        rcases rmMul_spec regS3 regS1 regJ regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            V inp s3 haU.reg₁_le (by rw [hs3_blk, hs3_J]; omega)
          with ⟨s4, hs4_mul, hs4_fr, hmul⟩
        have hs4_S3 : s4 regS3 = blk * paramJ n := by rw [hs4_mul, hs3_blk, hs3_J]
        have hs4_p : s4 regS2 = p := by rw [hs4_fr regS2 (by decide) (by decide) (by decide), hs3_p]
        have haTk := rmAdd_spec regS3 regS2 regS4 (by decide) (by decide) V inp s4 hmul.reg₁_le
          (by rw [hs4_S3, hs4_p]; omega)
        set s5 := regUpd (regUpd s4 regS3 (s4 regS3 + s4 regS2)) regS4 0
        have hs5_tk : s5 regS3 = blk * paramJ n + p := by simp [s5, hs4_S3, hs4_p]
        have hs5_V1 : s5 regV1 = 2 * n := by
          dsimp only [s5]
          rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
              hs4_fr regV1 (by decide) (by decide) (by decide)]
          simp [s3, hs2_pr regV1 (by decide), hV1, netV1]
        rcases rmCmpLt_spec regS0 regS3 regV1 regS4 regS5 (by decide) (by decide) (by decide) (by decide)
            V inp s5 haTk.reg₁_le h1V with ⟨s6, hs6_fl, hs6_fr, hcmp⟩
        have hs6_keep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem ∨ j = regEndU →
            s6 j = s3 j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl | rfl <;> (try simp at hv) <;> omega
          rw [hs6_fr j (hne regS0 (by decide)) (hne regS4 (by decide)) (hne regS5 (by decide))]
          dsimp only [s5]
          rw [regUpd_ne _ (hne regS4 (by decide)), regUpd_ne _ (hne regS3 (by decide)),
              hs4_fr j (hne regS3 (by decide)) (hne regS4 (by decide)) (hne regS5 (by decide))]
        have hs6_U : s6 regEndU = netV9 n + blk % paramL1 n := by
          rw [hs6_keep regEndU (Or.inr (Or.inr (Or.inr rfl))), hs3_U]
        have hs6_I : s6 regLoopI = k := by
          rw [hs6_keep regLoopI (Or.inr (Or.inl rfl))]
          dsimp only [s3]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
            hs2_fr regLoopI (by decide) (by decide) (by decide) (by decide) (by decide),
            hs1_fr regLoopI (by decide) (by decide) (by decide) (by decide) (by decide), hI]
        have hs6_tk : s6 regS3 = blk * paramJ n + p := by
          rw [hs6_fr regS3 (by decide) (by decide) (by decide), hs5_tk]
        have hs6_V10 : s6 regV10 = netV10 n := by
          rw [hs6_keep regV10 (Or.inl (by decide))]; simp [s3, hs2_pr regV10 (by decide), hV10]
        have hs6_V11 : s6 regV11 = netV11 n := by
          rw [hs6_keep regV11 (Or.inl (by decide))]; simp [s3, hs2_pr regV11 (by decide), hV11]
        have hbr : ∃ qB s7,
            (∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem ∨ j = regEndU → s7 j = s6 j) ∧
            s7 regEndV = (if blk * paramJ n + p < 2 * n then netV11 n + (blk * paramJ n + p)
                          else netV10 n + k) ∧
            RMExec (rmIfZero regS0 (rmSetAdd regEndV regV10 regLoopI) (rmSetAdd regEndV regV11 regS3)
                rmSetAddEntry rmSetAddEntry)
              V inp rmIfZeroEntry s6 qB s7 [] (120 * n + 10) := by
          by_cases hlt : blk * paramJ n + p < 2 * n
          · have hfl : s6 regS0 ≠ 0 := by rw [hs6_fl, hs5_tk, hs5_V1]; simp [hlt]
            have ha := rmSetAdd_spec regEndV regV11 regS3 (by decide) (by decide) (by decide)
              V inp s6 hcmp.reg₁_le (by rw [hs6_V11, hs6_tk]; omega)
            have hif := (rmIfZero_pos_spec regS0 (rmSetAdd regEndV regV10 regLoopI) rmSetAddEntry hfl ha).weaken
              (V₂ := V) (T₂ := 120 * n + 10) (le_refl _) (by rw [hs6_tk]; omega)
            refine ⟨_, _, ?_, by simp [hlt, hs6_V11, hs6_tk], hif⟩
            intro j hj
            have hne : ∀ r : Fin EncR, r = regS0 ∨ r = regEndV → j ≠ r := by
              intro r hr heq; have hv := congrArg Fin.val heq
              rcases hj with hj | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> (try simp at hv) <;> omega
            rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndV (Or.inr rfl))]
          · have hfl : s6 regS0 = 0 := by rw [hs6_fl, hs5_tk, hs5_V1]; simp [hlt]
            have ha := rmSetAdd_spec regEndV regV10 regLoopI (by decide) (by decide) (by decide)
              V inp s6 hcmp.reg₁_le (by rw [hs6_V10, hs6_I]; omega)
            have hif := (rmIfZero_zero_spec regS0 (rmSetAdd regEndV regV11 regS3) rmSetAddEntry hfl ha).weaken
              (V₂ := V) (T₂ := 120 * n + 10) (le_refl _) (by rw [hs6_I]; omega)
            refine ⟨_, _, ?_, by simp [hlt, hs6_V10, hs6_I], hif⟩
            intro j hj
            have hne : ∀ r : Fin EncR, r = regS0 ∨ r = regEndV → j ≠ r := by
              intro r hr heq; have hv := congrArg Fin.val heq
              rcases hj with hj | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> (try simp at hv) <;> omega
            rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndV (Or.inr rfl))]
        rcases hbr with ⟨qB, s7, hs7_keep, hs7_V, hif⟩
        have hs7_U : s7 regEndU = netV9 n + blk % paramL1 n := by
          rw [hs7_keep regEndU (Or.inr (Or.inr (Or.inr rfl))), hs6_U]
        have he := rmEmitEndPair_spec V inp s7 hif.reg₁_le
        have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
          intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
        have hact_sa : ∀ a b c : Fin EncR, rmSetAdd a b c rmSetAddEntry ≠ none := by
          intros; simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
        have hcomb := rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd1
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd2
            (rmChain_spec_inl (hact_sa _ _ _) haU
              (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hmul
                (rmChain_spec_inl (by simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]) haTk
                  (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp
                    (rmChain_spec_inl (by simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]) hif he))))))
        have hmul_le : blk * (2 * paramJ n + 3) ≤ 140 * n := by
          have : blk * (2 * paramJ n + 3) = 2 * (blk * paramJ n) + 3 * blk := by ring
          omega
        have hV_le : s7 regEndV ≤ 500 * n + 20 := by
          rw [hs7_V]; split_ifs <;> omega
        have hT : 15 * reg regLoopI + 2 * reg regTwoJ + 10 +
            (15 * s1 regS1 + 2 * s1 regL1 + 10 +
              (2 * s2 regS4 + 3 + (s3 regS1 * (2 * s3 regJ + 3) + 3 +
                (2 * s4 regS2 + 2 + (2 * min (s5 regS3) (s5 regV1) + 6 +
                  (120 * n + 10 + (2 * s7 regEndU + 2 * s7 regEndV + 6))))))) ≤
            4000 * n + 220 := by
          rw [hI, h2J, hs1_blk, hs1_L1, hs2_r', hs3_blk, hs3_J, hs4_p, hs5_tk, hs5_V1, hs7_U]
          have : min (blk * paramJ n + p) (2 * n) ≤ 2 * n := min_le_right _ _
          omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 4000 * n + 220) (by simp) hT
        simp only [List.nil_append, hs7_U, hs7_V] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem →
            regUpd s7 regS0 0 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
          have hj4 : j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem ∨ j = regEndU := by
            rcases hj with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), hs7_keep j hj4, hs6_keep j hj4]
          dsimp only [s3]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr rfl)),
              hs2_fr j (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))
                (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide))) (hne regS7 (Or.inl (by decide))),
              hs1_fr j (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmEmitEndPairExit)))))),
          regUpd s7 regS0 0, fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), ?_⟩
        simpa [rmB10Body, rmB10BodyEntry, endsB10, ovlTargetBit_eq, blk, p] using hfin)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * paramJ n * paramL n * (4000 * n + 220 + 2) + 3 ≤ 250000 * n ^ 2 + 15000 * n + 10 := by
    have hmul : 2 * paramJ n * paramL n * (4000 * n + 220 + 2) ≤ 54 * n * (4000 * n + 220 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 54 * n * (4000 * n + 220 + 2) = 216000 * n ^ 2 + 11988 * n := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 250000 * n ^ 2 + 15000 * n + 10) (le_refl _) hT⟩

/-- Block B11 (`2n` edges): `(netV11 n + k, netV12 n + k % n)`. -/
abbrev RMB11BodyQ : Type := RMSetAddQ ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ RMEmitEndPairQ))
abbrev RMEmitB11Q : Type := RMForRangeQ RMB11BodyQ

def rmB11Body : RMProg EncR RMB11BodyQ :=
  rmChain (rmSetAdd regEndU regV11 regLoopI)
    (rmChain (rmDivMod regS1 regS2 regLoopI regN regS3 regS4 regS5)
      (rmChain (rmSetAdd regEndV regV12 regS2) rmEmitEndPair rmEmitEndPairEntry)
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmB11BodyEntry : RMB11BodyQ := Sum.inl rmSetAddEntry

def rmEmitB11 : RMProg EncR RMEmitB11Q :=
  rmForRange regLoopI regLoopRem regV1 rmB11Body rmB11BodyEntry

lemma rmEmitB11_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB11 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB11 n e)))
        (5000 * n ^ 2 + 500 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hvc := netVertCount_le hn
  have hv12_le : netV11 n + 2 * n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13, netV12]; omega
  have hv13_le : netV12 n + n ≤ netVertCount n := by
    simp only [netVertCount, netV18, netV17, netV16, netV15, netV14, netV13]; omega
  have hcnt : reg₀ regV1 = 2 * n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases rmEdgeLoop_spec regV1 (by decide) rmB11Body rmB11BodyEntry V (2200 * n + 200) inp reg₀
      (fun e => emitEdgeBits (endsB11 n e)) hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hN : reg regN = n := hp'.1
        have hV11 : reg regV11 = netV11 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV12 : reg regV12 = netV12 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hk' : k < 2 * n := by omega
        have hmod_lt : k % n < n := Nat.mod_lt k (by omega)
        have haU := rmSetAdd_spec regEndU regV11 regLoopI (by decide) (by decide) (by decide)
          V inp reg hreg (by rw [hV11, hI]; omega)
        set s1 := regUpd (regUpd reg regEndU (reg regV11 + reg regLoopI)) regS0 0
        have hs1_I : s1 regLoopI = k := by simp [s1, hI]
        have hs1_N : s1 regN = n := by simp [s1, hN]
        rcases rmDivMod_spec regS1 regS2 regLoopI regN regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp s1 (by rw [hs1_N]; omega) haU.reg₁_le h1V
          with ⟨s2, _, hs2_r, hs2_fr, hd2⟩
        have hs2_r' : s2 regS2 = k % n := by rw [hs2_r, hs1_I, hs1_N]
        have hs2_V12 : s2 regV12 = netV12 n := by
          rw [hs2_fr regV12 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hV12]
        have haV := rmSetAdd_spec regEndV regV12 regS2 (by decide) (by decide) (by decide)
          V inp s2 hd2.reg₁_le (by rw [hs2_V12, hs2_r']; omega)
        set s3 := regUpd (regUpd s2 regEndV (s2 regV12 + s2 regS2)) regS0 0
        have hs3_U : s3 regEndU = netV11 n + k := by
          dsimp only [s3]
          rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
              hs2_fr regEndU (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s1, hV11, hI]
        have hs3_V : s3 regEndV = netV12 n + k % n := by simp [s3, hs2_V12, hs2_r']
        have he := rmEmitEndPair_spec V inp s3 haV.reg₁_le
        have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) haU
          (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd2
            (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) haV he))
        have hT : 2 * reg regLoopI + 3 + (15 * s1 regLoopI + 2 * s1 regN + 10 +
            (2 * s2 regS2 + 3 + (2 * s3 regEndU + 2 * s3 regEndV + 6))) ≤ 2200 * n + 200 := by
          rw [hI, hs1_I, hs1_N, hs2_r', hs3_U, hs3_V]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2200 * n + 200) (by simp) hT
        simp only [List.nil_append, hs3_U, hs3_V] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem →
            regUpd s3 regS0 0 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regEndU ∨ r = regEndV → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
          dsimp only [s3]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
              regUpd_ne _ (hne regEndV (Or.inr (Or.inr rfl))),
              hs2_fr j (hne regS1 (Or.inl (by decide))) (hne regS2 (Or.inl (by decide)))
                (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
          dsimp only [s1]
          rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl)))]
        exact ⟨_, _, fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * n * (2200 * n + 200 + 2) + 3 ≤ 5000 * n ^ 2 + 500 * n + 10 := by
    have : 2 * n * (2200 * n + 200 + 2) + 3 = 4400 * n ^ 2 + 404 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 5000 * n ^ 2 + 500 * n + 10) (le_refl _) hT⟩

/-! ### Edge Block Emitter B12 (Tree-Reduction Edges `endsB12`) -/

lemma treeEdgeOff_step {r j : ℕ} (hj : 1 ≤ j) :
    treeEdgeOff r (j + 1) = treeEdgeOff r j + (2 * j + 1) * 2 ^ (r - j) := by
  cases j with
  | zero => omega
  | succ _ => rfl

lemma treeVertOff_step {r j : ℕ} (hj : 1 ≤ j) :
    treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := by
  cases j with
  | zero => omega
  | succ _ => rfl

lemma treeEdgeOff_mono (r : ℕ) {a b : ℕ} (h : a ≤ b) : treeEdgeOff r a ≤ treeEdgeOff r b := by
  induction h with
  | refl => exact le_refl _
  | @step m _ ih =>
    cases m with
    | zero => exact ih
    | succ k =>
      have : treeEdgeOff r (k + 2) = treeEdgeOff r (k + 1) + (2 * (k + 1) + 1) * 2 ^ (r - (k + 1)) := rfl
      change treeEdgeOff r a ≤ treeEdgeOff r (k + 2)
      omega

lemma treeVertOff_mono (r : ℕ) {a b : ℕ} (h : a ≤ b) : treeVertOff r a ≤ treeVertOff r b := by
  induction h with
  | refl => exact le_refl _
  | @step m _ ih =>
    cases m with
    | zero => exact ih
    | succ k =>
      have : treeVertOff r (k + 2) = treeVertOff r (k + 1) + ((k + 1) + 1) * 2 ^ (r - (k + 1)) := rfl
      change treeVertOff r a ≤ treeVertOff r (k + 2)
      omega

lemma netV15_add_treeVertOff_le (n : ℕ) :
    netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ netVertCount n := by
  simp only [netVertCount, netV18, netV17, netV16]; omega

lemma bitIdx_eq_div2 (j w : ℕ) : (if w = 2 * j then j else w / 2) = w / 2 := by
  split_ifs with h <;> omega

/-- Pre-loop setup for B12: loads `regLoopJ := treeEdgeOff (treeLog n + 1) (treeLog n + 2)`. -/
abbrev RMB12CountQ : Type :=
  RMSetConstQ 10 ⊕ (RMMulQ ⊕ (RMSetAddQ ⊕ (Fin 8 ⊕ RMSubQ)))

def rmB12Count : RMProg EncR RMB12CountQ :=
  rmChain (rmSetConst regS1 10)
    (rmChain (rmMul regLoopJ regS1 regTreeM regS2 regS3)
      (rmChain (rmSetAdd regS1 regTreeLog regTreeLog)
        (rmChain (rmAddConst regS1 7) (rmSub regLoopJ regS1 regS0) rmSubEntry)
        (Sum.inl ⟨0, by omega⟩))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmMulEntry)

def rmB12CountEntry : RMB12CountQ := Sum.inl rmSetConstEntry
def rmB12CountExit : RMB12CountQ := Sum.inr (Sum.inr (Sum.inr (Sum.inr rmSubExit)))

lemma rmB12Count_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ r1 : RegState EncR,
      PreservedRegs r1 reg₀ ∧
      r1 regLoopJ = treeEdgeOff (treeLog n + 1) (treeLog n + 2) ∧
      RMExec rmB12Count V inp rmB12CountEntry reg₀ rmB12CountExit r1 [] (200 * n + 50) := by
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hTL : reg₀ regTreeLog = treeLog n := hp.2.2.2.2.2.2.2.2.2.2.1
  have hs1 := rmSetConst_spec regS1 10 V inp reg₀ hreg₀ (by omega)
  set r1 := regUpd reg₀ regS1 10
  rcases rmMul_spec regLoopJ regS1 regTreeM regS2 regS3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r1 hs1.reg₁_le (by simp [r1, hTM]; omega)
    with ⟨r2, h2_J, h2_fr, hm2⟩
  have h2_J' : r2 regLoopJ = 10 * treeM n := by rw [h2_J]; simp [r1, hTM]
  have h2_TL : r2 regTreeLog = treeLog n := by
    rw [h2_fr regTreeLog (by decide) (by decide) (by decide)]; simp [r1, hTL]
  have ha3 := rmSetAdd_spec regS1 regTreeLog regTreeLog (by decide) (by decide) (by decide)
    V inp r2 hm2.reg₁_le (by rw [h2_TL]; omega)
  set r3 := regUpd (regUpd r2 regS1 (r2 regTreeLog + r2 regTreeLog)) regS0 0
  have h3_S1 : r3 regS1 = 2 * treeLog n := by simp [r3, h2_TL]; omega
  have h3_J : r3 regLoopJ = 10 * treeM n := by simp [r3, h2_J']
  have hc4 := rmAddConst_spec regS1 7 V inp r3 ha3.reg₁_le (by rw [h3_S1]; omega)
  set r4 := regUpd r3 regS1 (r3 regS1 + 7)
  have h4_S1 : r4 regS1 = 2 * treeLog n + 7 := by simp [r4, h3_S1]
  have h4_J : r4 regLoopJ = 10 * treeM n := by simp [r4, h3_J]
  have hsub5 := rmSub_spec regLoopJ regS1 regS0 (by decide) V inp r4 hc4.reg₁_le
  set r5 := regUpd (regUpd r4 regLoopJ (r4 regLoopJ - r4 regS1)) regS0 0
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hs1
    (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hm2
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha3
        (rmChain_spec_inl (by simp [rmAddConst]) hc4 hsub5)))
  have hT : 1 + 10 + (r1 regS1 * (2 * r1 regTreeM + 3) + 3 + (2 * r2 regTreeLog + 3 + (7 + (2 * r4 regS1 + 2)))) ≤
      200 * n + 50 := by
    have hr1S1 : r1 regS1 = 10 := by simp [r1]
    have hr1TM : r1 regTreeM = treeM n := by simp [r1, hTM]
    rw [hr1S1, hr1TM, h2_TL, h4_S1]; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 200 * n + 50) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨r5, fun k hk => ?_, by simp [r5, h4_J, h4_S1, treeEdgeOff_net], hfin⟩
  have hne : ∀ r : Fin EncR, 41 ≤ r.val → k ≠ r := fun r hr heq => by
    have := congrArg Fin.val heq; omega
  dsimp only [r5, r4, r3]
  rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regLoopJ (by decide)),
      regUpd_ne _ (hne regS1 (by decide)), regUpd_ne _ (hne regS0 (by decide)),
      regUpd_ne _ (hne regS1 (by decide)),
      h2_fr k (hne regLoopJ (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))]
  dsimp only [r1]; rw [regUpd_ne _ (hne regS1 (by decide))]

/-- B12 loop-guard helper: computes `regS5 := (2 * j + 1) * twoPow` and `regS0 := (blk ≤ rem ? 1 : 0)`. -/
abbrev RMB12TestQ : Type := RMSetAddQ ⊕ (Bool ⊕ (RMMulQ ⊕ Fin 8))

def rmB12Test : RMProg EncR RMB12TestQ :=
  rmChain (rmSetAdd regS1 regLoopJ regLoopJ)
    (rmChain (rmInc regS1)
      (rmChain (rmMul regS5 regS1 regLoopW regS2 regS3)
        (rmCmpGe regS0 regLoopNode regS5 regS1 regS2) 0)
      (Sum.inl rmMulEntry))
    (Sum.inl false)

def rmB12TestEntry : RMB12TestQ := Sum.inl rmSetAddEntry
def rmB12TestExit : RMB12TestQ := Sum.inr (Sum.inr (Sum.inr 7))

lemma rmB12Test_spec (n V j rem : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hJ : reg regLoopJ = j) (hN : reg regLoopNode = rem)
    (hW : reg regLoopW = 2 ^ (treeLog n + 1 - j)) :
    let blk := (2 * j + 1) * 2 ^ (treeLog n + 1 - j)
    ∃ r1 : RegState EncR,
      r1 regS5 = blk ∧
      r1 regS0 = (if blk ≤ rem then 1 else 0) ∧
      (∀ k : Fin EncR, k ≠ regS0 → k ≠ regS1 → k ≠ regS2 → k ≠ regS3 → k ≠ regS5 → r1 k = reg k) ∧
      RMExec rmB12Test V inp rmB12TestEntry reg rmB12TestExit r1 [] (100 * n + 30) := by
  intro blk
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have he_le : treeEdgeOff (treeLog n + 1) (treeLog n + 2) ≤ 20 * n := by
    rw [treeEdgeOff_net]; omega
  have hblk_le : blk ≤ 20 * n := by
    have h1 := treeEdgeOff_step (r := treeLog n + 1) hj1
    have h2 := treeEdgeOff_mono (treeLog n + 1) (show j + 1 ≤ treeLog n + 2 by omega)
    dsimp only [blk]; omega
  have ha1 := rmSetAdd_spec regS1 regLoopJ regLoopJ (by decide) (by decide) (by decide)
    V inp reg hreg (by rw [hJ]; omega)
  set s1 := regUpd (regUpd reg regS1 (reg regLoopJ + reg regLoopJ)) regS0 0
  have hs1_S1 : s1 regS1 = 2 * j := by simp [s1, hJ]; omega
  have hi2 := rmInc_spec regS1 V inp s1 ha1.reg₁_le (by rw [hs1_S1]; omega)
  set s2 := regUpd s1 regS1 (s1 regS1 + 1)
  have hs2_S1 : s2 regS1 = 2 * j + 1 := by simp [s2, hs1_S1]
  have hs2_W : s2 regLoopW = 2 ^ (treeLog n + 1 - j) := by simp [s2, s1, hW]
  rcases rmMul_spec regS5 regS1 regLoopW regS2 regS3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp s2 hi2.reg₁_le (by rw [hs2_S1, hs2_W]; dsimp only [blk] at hblk_le; omega)
    with ⟨s3, hs3_blk, hs3_fr, hm3⟩
  have hs3_S5 : s3 regS5 = blk := by rw [hs3_blk, hs2_S1, hs2_W]
  have hs3_N : s3 regLoopNode = rem := by
    rw [hs3_fr regLoopNode (by decide) (by decide) (by decide)]; simp [s2, s1, hN]
  rcases rmCmpGe_spec regS0 regLoopNode regS5 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
      V inp s3 hm3.reg₁_le h1V with ⟨s4, hs4_fl, hs4_fr, hcmp4⟩
  have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha1
    (rmChain_spec_inl (by simp [rmInc]) hi2
      (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hm3 hcmp4))
  have hmul_le : (2 * j + 1) * (2 * 2 ^ (treeLog n + 1 - j) + 3) ≤ 46 * n + 9 := by
    have : (2 * j + 1) * (2 * 2 ^ (treeLog n + 1 - j) + 3) = 2 * blk + 3 * (2 * j + 1) := by
      dsimp only [blk]; ring
    omega
  have hT : 2 * reg regLoopJ + 3 + (1 + (s2 regS1 * (2 * s2 regLoopW + 3) + 3 +
      (2 * min (s3 regLoopNode) (s3 regS5) + 6))) ≤ 100 * n + 30 := by
    rw [hJ, hs2_S1, hs2_W, hs3_N, hs3_S5]
    have : min rem blk ≤ blk := min_le_right _ _
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 100 * n + 30) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨s4, by rw [hs4_fr regS5 (by decide) (by decide) (by decide), hs3_S5],
    by rw [hs4_fl, hs3_N, hs3_S5], ?_, hfin⟩
  intro k h0 h1 h2 h3 h5
  rw [hs4_fr k h0 h1 h2, hs3_fr k h5 h2 h3]
  dsimp only [s2, s1]
  rw [regUpd_ne _ h1, regUpd_ne _ h0, regUpd_ne _ h1]

/-- One iteration of the `decodeTreeEdgeAux` while-loop in B12. -/
abbrev RMB12StepQ : Type :=
  RMSubQ ⊕ (Bool ⊕ (Bool ⊕ (RMMulQ ⊕ (RMAddQ ⊕
    (RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (Bool ⊕ (Bool ⊕ RMB12TestQ))))))))

def rmB12Step : RMProg EncR RMB12StepQ :=
  rmChain (rmSub regLoopNode regS5 regS1)
    (rmChain (rmCopy regS1 regLoopJ)
      (rmChain (rmInc regS1)
        (rmChain (rmMul regS2 regS1 regLoopW regS3 regS4)
          (rmChain (rmAdd regS7 regS2 regS1)
            (rmChain (rmSetConst regS1 2)
              (rmChain (rmDivMod regS2 regS3 regLoopW regS1 regS4 regS5 regS6)
                (rmChain (rmCopy regLoopW regS2)
                  (rmChain (rmInc regLoopJ) rmB12Test rmB12TestEntry)
                  (Sum.inl false))
                (Sum.inl false))
              (Sum.inl rmDivModEntry))
            (Sum.inl rmSetConstEntry))
          (Sum.inl rmAddEntry))
        (Sum.inl rmMulEntry))
      (Sum.inl false))
    (Sum.inl false)

def rmB12StepEntry : RMB12StepQ := Sum.inl rmSubEntry
def rmB12StepExit : RMB12StepQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmB12TestExit))))))))

lemma rmB12Step_spec (n V j rem : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j < treeLog n + 1)
    (hJ : reg regLoopJ = j) (hN : reg regLoopNode = rem)
    (hW : reg regLoopW = 2 ^ (treeLog n + 1 - j))
    (hVO : reg regS7 = treeVertOff (treeLog n + 1) j)
    (hBlk : reg regS5 = (2 * j + 1) * 2 ^ (treeLog n + 1 - j)) :
    let blk := (2 * j + 1) * 2 ^ (treeLog n + 1 - j)
    let blkNext := (2 * (j + 1) + 1) * 2 ^ (treeLog n + 1 - (j + 1))
    ∃ r1 : RegState EncR,
      r1 regLoopJ = j + 1 ∧
      r1 regLoopNode = rem - blk ∧
      r1 regLoopW = 2 ^ (treeLog n + 1 - (j + 1)) ∧
      r1 regS7 = treeVertOff (treeLog n + 1) (j + 1) ∧
      r1 regS5 = blkNext ∧
      r1 regS0 = (if blkNext ≤ rem - blk then 1 else 0) ∧
      PreservedRegs r1 reg ∧
      r1 regLoopI = reg regLoopI ∧
      r1 regLoopRem = reg regLoopRem ∧
      RMExec rmB12Step V inp rmB12StepEntry reg rmB12StepExit r1 [] (260 * n + 80) := by
  intro blk blkNext
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hpow_le : 2 ^ (treeLog n + 1 - j) ≤ 2 * n := by
    calc 2 ^ (treeLog n + 1 - j) ≤ 2 ^ treeLog n := Nat.pow_le_pow_right (by decide) (by omega)
      _ = treeM n := rfl
      _ ≤ 2 * n := hM_le
  have hpow_div : 2 ^ (treeLog n + 1 - j) / 2 = 2 ^ (treeLog n + 1 - (j + 1)) := by
    have heq : treeLog n + 1 - j = (treeLog n + 1 - (j + 1)) + 1 := by omega
    rw [heq, pow_succ']; omega
  have hblk_le : blk ≤ 20 * n := by
    have h1 := treeEdgeOff_step (r := treeLog n + 1) hj1
    have h2 := treeEdgeOff_mono (treeLog n + 1) (show j + 1 ≤ treeLog n + 2 by omega)
    have h3 : treeEdgeOff (treeLog n + 1) (treeLog n + 2) ≤ 20 * n := by rw [treeEdgeOff_net]; omega
    dsimp only [blk]; omega
  have hvo_next_le : treeVertOff (treeLog n + 1) (j + 1) ≤ 12 * n := by
    have h1 := treeVertOff_mono (treeLog n + 1) (show j + 1 ≤ treeLog n + 2 by omega)
    have h2 : treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ 12 * n := by rw [treeVertOff_net]; omega
    omega
  have hvostep := treeVertOff_step (r := treeLog n + 1) hj1
  have hs1 := rmSub_spec regLoopNode regS5 regS1 (by decide) V inp reg hreg
  set r1 := regUpd (regUpd reg regLoopNode (reg regLoopNode - reg regS5)) regS1 0
  have h1_N : r1 regLoopNode = rem - blk := by simp [r1, hN, hBlk, blk]
  have h1_J : r1 regLoopJ = j := by simp [r1, hJ]
  have h1_W : r1 regLoopW = 2 ^ (treeLog n + 1 - j) := by simp [r1, hW]
  have h1_VO : r1 regS7 = treeVertOff (treeLog n + 1) j := by simp [r1, hVO]
  have hc2 := rmCopy_spec regS1 regLoopJ V inp r1 hs1.reg₁_le
  set r2 := regUpd r1 regS1 (r1 regLoopJ)
  have hi3 := rmInc_spec regS1 V inp r2 hc2.reg₁_le (by simp [r2, h1_J]; omega)
  set r3 := regUpd r2 regS1 (r2 regS1 + 1)
  have h3_S1 : r3 regS1 = j + 1 := by simp [r3, r2, h1_J]
  have h3_W : r3 regLoopW = 2 ^ (treeLog n + 1 - j) := by simp [r3, r2, h1_W]
  rcases rmMul_spec regS2 regS1 regLoopW regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp r3 hi3.reg₁_le (by rw [h3_S1, h3_W]; omega)
    with ⟨r4, h4_S2, h4_fr, hm4⟩
  have h4_S2' : r4 regS2 = (j + 1) * 2 ^ (treeLog n + 1 - j) := by rw [h4_S2, h3_S1, h3_W]
  have h4_VO : r4 regS7 = treeVertOff (treeLog n + 1) j := by
    rw [h4_fr regS7 (by decide) (by decide) (by decide)]; simp [r3, r2, h1_VO]
  have ha5 := rmAdd_spec regS7 regS2 regS1 (by decide) (by decide) V inp r4 hm4.reg₁_le
    (by rw [h4_VO, h4_S2']; omega)
  set r5 := regUpd (regUpd r4 regS7 (r4 regS7 + r4 regS2)) regS1 0
  have h5_VO : r5 regS7 = treeVertOff (treeLog n + 1) (j + 1) := by
    simp [r5, h4_VO, h4_S2', hvostep]
  have h5_W : r5 regLoopW = 2 ^ (treeLog n + 1 - j) := by
    dsimp only [r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h4_fr regLoopW (by decide) (by decide) (by decide), h3_W]
  have hsc6 := rmSetConst_spec regS1 2 V inp r5 ha5.reg₁_le (by omega)
  set r6 := regUpd r5 regS1 2
  have h6_W : r6 regLoopW = 2 ^ (treeLog n + 1 - j) := by simp [r6, h5_W]
  rcases rmDivMod_spec regS2 regS3 regLoopW regS1 regS4 regS5 regS6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      V inp r6 (by simp [r6]) hsc6.reg₁_le h1V
    with ⟨r7, h7_q, _, h7_fr, hd7⟩
  have h7_S2 : r7 regS2 = 2 ^ (treeLog n + 1 - (j + 1)) := by
    rw [h7_q, h6_W]; simp [r6, hpow_div]
  have h7_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨
      k = regLoopJ ∨ k = regLoopNode ∨ k = regS7 → r7 k = r5 k := by
    intro k hk
    have hne : ∀ r : Fin EncR, r = regS1 ∨ r = regS2 ∨ r = regS3 ∨ r = regS4 ∨ r = regS5 ∨ r = regS6 → k ≠ r := by
      intro r hr heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp at hv) <;> omega
    rw [h7_fr k (hne regS2 (Or.inr (Or.inl rfl))) (hne regS3 (Or.inr (Or.inr (Or.inl rfl))))
        (hne regS4 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (hne regS5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (hne regS6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))]
    dsimp only [r6]; rw [regUpd_ne _ (hne regS1 (Or.inl rfl))]
  have hc8 := rmCopy_spec regLoopW regS2 V inp r7 hd7.reg₁_le
  set r8 := regUpd r7 regLoopW (r7 regS2)
  have h8_J : r8 regLoopJ = j := by
    dsimp only [r8]; rw [regUpd_ne _ (by decide), h7_keep regLoopJ (by omega)]
    dsimp only [r5]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
      h4_fr regLoopJ (by decide) (by decide) (by decide)]; simp [r3, r2, h1_J]
  have hi9 := rmInc_spec regLoopJ V inp r8 hc8.reg₁_le (by rw [h8_J]; omega)
  set r9 := regUpd r8 regLoopJ (r8 regLoopJ + 1)
  have h9_J : r9 regLoopJ = j + 1 := by simp [r9, h8_J]
  have h9_W : r9 regLoopW = 2 ^ (treeLog n + 1 - (j + 1)) := by simp [r9, r8, h7_S2]
  have h9_N : r9 regLoopNode = rem - blk := by
    dsimp only [r9, r8]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h7_keep regLoopNode (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
    dsimp only [r5]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h4_fr regLoopNode (by decide) (by decide) (by decide)]; simp [r3, r2, h1_N]
  have h9_VO : r9 regS7 = treeVertOff (treeLog n + 1) (j + 1) := by
    dsimp only [r9, r8]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        h7_keep regS7 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), h5_VO]
  rcases rmB12Test_spec n V (j + 1) (rem - blk) inp r9 hn hi9.reg₁_le hV
      (by omega) (by omega) h9_J h9_N h9_W
    with ⟨r10, h10_S5, h10_S0, h10_fr, ht10⟩
  have hcomb := rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs1
    (rmChain_spec_inl (by simp [rmCopy]) hc2
      (rmChain_spec_inl (by simp [rmInc]) hi3
        (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hm4
          (rmChain_spec_inl (by simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]) ha5
            (rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc6
              (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd7
                (rmChain_spec_inl (by simp [rmCopy]) hc8
                  (rmChain_spec_inl (by simp [rmInc]) hi9 ht10))))))))
  have hmul_le : (j + 1) * (2 * 2 ^ (treeLog n + 1 - j) + 3) ≤ 30 * n + 6 := by
    have : (j + 1) * (2 * 2 ^ (treeLog n + 1 - j) + 3) =
        2 * ((j + 1) * 2 ^ (treeLog n + 1 - j)) + 3 * (j + 1) := by ring
    omega
  have hT : 2 * reg regS5 + 2 + (1 + (1 + (r3 regS1 * (2 * r3 regLoopW + 3) + 3 +
      (2 * r4 regS2 + 2 + (1 + 2 + (15 * r6 regLoopW + 2 * r6 regS1 + 10 + (1 + (1 + (100 * n + 30))))))))) ≤
      260 * n + 80 := by
    have hr6S1 : r6 regS1 = 2 := by simp [r6]
    rw [hBlk, h3_S1, h3_W, h4_S2', h6_W, hr6S1]; dsimp only [blk] at hblk_le; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 260 * n + 80) (by simp) hT
  simp only [List.nil_append] at hfin
  have h10_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem → r10 k = reg k := by
    intro k hk
    have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) ∨ r = regLoopJ ∨ r = regLoopNode ∨ r = regLoopW →
        k ≠ r := by
      intro r hr heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl <;> rcases hr with ⟨h1, h2⟩ | rfl | rfl | rfl <;> (try simp at hv) <;> omega
    have hk6 : k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨ k = regLoopNode ∨ k = regS7 := by
      rcases hk with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))
    rw [h10_fr k (hne regS0 (Or.inl (by decide))) (hne regS1 (Or.inl (by decide)))
          (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
    dsimp only [r9, r8]
    rw [regUpd_ne _ (hne regLoopJ (Or.inr (Or.inl rfl))), regUpd_ne _ (hne regLoopW (Or.inr (Or.inr (Or.inr rfl)))),
        h7_keep k hk6]
    dsimp only [r5]
    rw [regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regS7 (Or.inl (by decide))),
        h4_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))]
    dsimp only [r3, r2, r1]
    rw [regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
        regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regLoopNode (Or.inr (Or.inr (Or.inl rfl))))]
  refine ⟨r10,
    by rw [h10_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide), h9_J],
    by rw [h10_fr regLoopNode (by decide) (by decide) (by decide) (by decide) (by decide), h9_N],
    by rw [h10_fr regLoopW (by decide) (by decide) (by decide) (by decide) (by decide), h9_W],
    by rw [h10_fr regS7 (by decide) (by decide) (by decide) (by decide) (by decide), h9_VO],
    h10_S5, h10_S0, fun k hk => h10_keep k (Or.inl hk),
    h10_keep regLoopI (Or.inr (Or.inl rfl)), h10_keep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩

lemma rmB12While_spec (n V : ℕ) (inp : List Bool) (hn : 1 ≤ n) (hV : 500 * n + 20 ≤ V) :
    ∀ (fuel j rem : ℕ) (reg : RegState EncR),
      1 ≤ j →
      j + fuel = treeLog n + 2 →
      treeEdgeOff (treeLog n + 1) j + rem < treeEdgeOff (treeLog n + 1) (treeLog n + 2) →
      (∀ i, reg i ≤ V) →
      reg regLoopJ = j →
      reg regLoopNode = rem →
      reg regLoopW = 2 ^ (treeLog n + 1 - j) →
      reg regS7 = treeVertOff (treeLog n + 1) j →
      reg regS5 = (2 * j + 1) * 2 ^ (treeLog n + 1 - j) →
      reg regS0 = (if (2 * j + 1) * 2 ^ (treeLog n + 1 - j) ≤ rem then 1 else 0) →
      let t := decodeTreeEdgeAux (treeLog n + 1) rem fuel j
      ∃ r1 : RegState EncR,
        1 ≤ t.1 ∧ t.1 ≤ treeLog n + 1 ∧
        r1 regLoopJ = t.1 ∧
        r1 regLoopNode < (2 * t.1 + 1) * 2 ^ (treeLog n + 1 - t.1) ∧
        r1 regLoopNode / (2 * t.1 + 1) = t.2.1 ∧
        r1 regLoopNode % (2 * t.1 + 1) = t.2.2 ∧
        r1 regLoopW = 2 ^ (treeLog n + 1 - t.1) ∧
        r1 regS7 = treeVertOff (treeLog n + 1) t.1 ∧
        PreservedRegs r1 reg ∧
        r1 regLoopI = reg regLoopI ∧
        r1 regLoopRem = reg regLoopRem ∧
        RMExec (rmWhile regS0 rmB12Step rmB12StepEntry) V inp rmWhileEntry reg rmWhileExit r1 []
          (fuel * (260 * n + 82) + 2)
  | 0, j, rem, reg, _, hjf, hlt, _, _, _, _, _, _, _ => by
    have : j = treeLog n + 2 := by omega
    subst this; omega
  | fuel + 1, j, rem, reg, hj1, hjf, hlt, hreg, hJ, hN, hW, hVO, hBlk, hFl => by
    set r := treeLog n + 1
    set blk := (2 * j + 1) * 2 ^ (r - j)
    by_cases hlt_blk : rem < blk
    · have hfl0 : reg regS0 = 0 := by rw [hFl]; simp [show ¬ (blk ≤ rem) by omega]
      have hw := (rmWhile_zero regS0 rmB12Step rmB12StepEntry V inp reg hfl0 hreg).weaken
        (V₂ := V) (T₂ := (fuel + 1) * (260 * n + 82) + 2) (le_refl _) (by omega)
      refine ⟨reg, by simp [decodeTreeEdgeAux, r, blk, hlt_blk, hj1],
        by simp [decodeTreeEdgeAux, r, blk, hlt_blk]; omega, ?_, ?_, ?_, ?_, ?_, ?_,
        PreservedRegs.refl reg, rfl, rfl, hw⟩ <;>
        simp [decodeTreeEdgeAux, r, blk, hlt_blk, hJ, hN, hW, hVO]
    · have hge_blk : blk ≤ rem := by omega
      have hfl1 : reg regS0 ≠ 0 := by rw [hFl]; simp [hge_blk]
      have hjr : j < r := by
        by_contra hnot
        have hjeq : j = r := by omega
        have hstep := treeEdgeOff_step (r := r) hj1
        dsimp only [blk] at hge_blk
        rw [hjeq] at hstep hlt hge_blk
        have : r + 1 = treeLog n + 2 := by omega
        rw [this] at hstep; omega
      rcases rmB12Step_spec n V j rem inp reg hn hreg hV hj1 hjr hJ hN hW hVO hBlk
        with ⟨r1, h1J, h1N, h1W, h1VO, h1Blk, h1Fl, h1pr, h1I, h1rem, hstep⟩
      have hlt_next : treeEdgeOff r (j + 1) + (rem - blk) < treeEdgeOff r (treeLog n + 2) := by
        have := treeEdgeOff_step (r := r) hj1; dsimp only [blk]; omega
      rcases rmB12While_spec n V inp hn hV fuel (j + 1) (rem - blk) r1
          (by omega) (by omega) hlt_next hstep.reg₁_le h1J h1N h1W h1VO h1Blk h1Fl
        with ⟨r2, ht1, htr, h2J, h2Nlt, h2div, h2mod, h2W, h2VO, h2pr, h2I, h2rem, hrest⟩
      have hw := rmWhile_step regS0 rmB12Step hfl1 hstep hrest
      have hT : 2 + (260 * n + 80) + (fuel * (260 * n + 82) + 2) =
          (fuel + 1) * (260 * n + 82) + 2 := by ring
      rw [max_self, List.nil_append, hT] at hw
      have hdec : decodeTreeEdgeAux r rem (fuel + 1) j = decodeTreeEdgeAux r (rem - blk) fuel (j + 1) := by
        simp [decodeTreeEdgeAux, blk, hlt_blk]
      refine ⟨r2, by rw [hdec]; exact ht1, by rw [hdec]; exact htr,
        by rw [hdec]; exact h2J, by rw [hdec]; exact h2Nlt,
        by rw [hdec]; exact h2div, by rw [hdec]; exact h2mod,
        by rw [hdec]; exact h2W, by rw [hdec]; exact h2VO,
        h2pr.trans h1pr, by rw [h2I, h1I], by rw [h2rem, h1rem], hw⟩

/-- Post-while B12 finalizer: extracts `node, w, vertOffNext, baseSrc`. -/
abbrev RMB12FinQ : Type :=
  RMSetAddQ ⊕ (Bool ⊕ (RMDivModQ ⊕ (Bool ⊕ (Bool ⊕
    (Bool ⊕ (Bool ⊕ (RMMulQ ⊕ (RMSetAddQ ⊕ (RMMulQ ⊕ (RMAddQ ⊕ RMAddQ))))))))))

def rmB12Fin : RMProg EncR RMB12FinQ :=
  rmChain (rmSetAdd regS1 regLoopJ regLoopJ)
    (rmChain (rmInc regS1)
      (rmChain (rmDivMod regS2 regS3 regLoopNode regS1 regS4 regS5 regS6)
        (rmChain (rmCopy regLoopNode regS2)
          (rmChain (rmCopy regS6 regS3)
            (rmChain (rmCopy regS1 regLoopJ)
              (rmChain (rmInc regS1)
                (rmChain (rmMul regS2 regS1 regLoopW regS3 regS4)
                  (rmChain (rmSetAdd regLoopW regS7 regS2)
                    (rmChain (rmMul regS2 regLoopNode regS1 regS3 regS4)
                      (rmChain (rmAdd regS7 regV15 regS0) (rmAdd regS7 regS2 regS0) rmAddEntry)
                      (Sum.inl rmAddEntry))
                    (Sum.inl rmMulEntry))
                  (Sum.inl rmSetAddEntry))
                (Sum.inl rmMulEntry))
              (Sum.inl false))
            (Sum.inl false))
          (Sum.inl false))
        (Sum.inl false))
      (Sum.inl rmDivModEntry))
    (Sum.inl false)

def rmB12FinEntry : RMB12FinQ := Sum.inl rmSetAddEntry
def rmB12FinExit : RMB12FinQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmAddExit))))))))))

lemma rmB12Fin_spec (n V j rem : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hJ : reg regLoopJ = j) (hN : reg regLoopNode = rem)
    (hNlt : rem < (2 * j + 1) * 2 ^ (treeLog n + 1 - j))
    (hW : reg regLoopW = 2 ^ (treeLog n + 1 - j))
    (hVO : reg regS7 = treeVertOff (treeLog n + 1) j) :
    let r := treeLog n + 1
    let node := rem / (2 * j + 1)
    let w := rem % (2 * j + 1)
    ∃ r1 : RegState EncR,
      PreservedRegs r1 reg ∧
      r1 regLoopI = reg regLoopI ∧
      r1 regLoopRem = reg regLoopRem ∧
      r1 regLoopJ = j ∧
      r1 regLoopNode = node ∧
      r1 regS6 = w ∧
      r1 regLoopW = treeVertOff r (j + 1) ∧
      r1 regS7 = netV15 n + treeVertOff r j + node * (j + 1) ∧
      RMExec rmB12Fin V inp rmB12FinEntry reg rmB12FinExit r1 [] (2000 * n + 200) := by
  intro r node w
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
    simpa [r] using netV15_add_treeVertOff_le n
  have hblk_le : (2 * j + 1) * 2 ^ (r - j) ≤ 20 * n := by
    have h1 := treeEdgeOff_step (r := r) hj1
    have h2 := treeEdgeOff_mono r (show j + 1 ≤ r + 1 by omega)
    have h3 : treeEdgeOff r (r + 1) ≤ 20 * n := by
      have hr1 : r + 1 = treeLog n + 2 := by omega
      rw [hr1, treeEdgeOff_net]; omega
    omega
  have hvo_next_le : treeVertOff r (j + 1) ≤ treeVertOff r (r + 1) :=
    treeVertOff_mono r (by omega)
  have hvo_12 : treeVertOff r (r + 1) ≤ 12 * n := by
    have hr1 : r + 1 = treeLog n + 2 := by omega
    rw [hr1, treeVertOff_net]; omega
  have hvostep := treeVertOff_step (r := r) hj1
  have hnode_lt : node < 2 ^ (r - j) := Nat.div_lt_of_lt_mul hNlt
  have hnode_mul_le : node * (j + 1) ≤ (j + 1) * 2 ^ (r - j) := by
    calc node * (j + 1) ≤ 2 ^ (r - j) * (j + 1) := Nat.mul_le_mul_right _ (le_of_lt hnode_lt)
      _ = (j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  have hV15 : reg regV15 = netV15 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha1 := rmSetAdd_spec regS1 regLoopJ regLoopJ (by decide) (by decide) (by decide)
    V inp reg hreg (by rw [hJ]; omega)
  set s1 := regUpd (regUpd reg regS1 (reg regLoopJ + reg regLoopJ)) regS0 0
  have hs1_S1 : s1 regS1 = 2 * j := by simp [s1, hJ]; omega
  have hi2 := rmInc_spec regS1 V inp s1 ha1.reg₁_le (by rw [hs1_S1]; omega)
  set s2 := regUpd s1 regS1 (s1 regS1 + 1)
  have hs2_S1 : s2 regS1 = 2 * j + 1 := by simp [s2, hs1_S1]
  have hs2_N : s2 regLoopNode = rem := by simp [s2, s1, hN]
  rcases rmDivMod_spec regS2 regS3 regLoopNode regS1 regS4 regS5 regS6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      V inp s2 (by rw [hs2_S1]; omega) hi2.reg₁_le h1V
    with ⟨s3, hs3_q, hs3_r, hs3_fr, hd3⟩
  have hs3_S2 : s3 regS2 = node := by rw [hs3_q, hs2_N, hs2_S1]
  have hs3_S3 : s3 regS3 = w := by rw [hs3_r, hs2_N, hs2_S1]
  have hs3_J : s3 regLoopJ = j := by
    rw [hs3_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s2, s1, hJ]
  have hs3_W : s3 regLoopW = 2 ^ (r - j) := by
    rw [hs3_fr regLoopW (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s2, s1, hW, r]
  have hs3_VO : s3 regS7 = treeVertOff r j := by
    rw [hs3_fr regS7 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s2, s1, hVO, r]
  have hs3_V15 : s3 regV15 = netV15 n := by
    rw [hs3_fr regV15 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s2, s1, hV15]
  have hc4 := rmCopy_spec regLoopNode regS2 V inp s3 hd3.reg₁_le
  set s4 := regUpd s3 regLoopNode (s3 regS2)
  have hc5 := rmCopy_spec regS6 regS3 V inp s4 hc4.reg₁_le
  set s5 := regUpd s4 regS6 (s4 regS3)
  have hc6 := rmCopy_spec regS1 regLoopJ V inp s5 hc5.reg₁_le
  set s6 := regUpd s5 regS1 (s5 regLoopJ)
  have hi7 := rmInc_spec regS1 V inp s6 hc6.reg₁_le (by simp [s6, s5, s4, hs3_J]; omega)
  set s7 := regUpd s6 regS1 (s6 regS1 + 1)
  have hs7_S1 : s7 regS1 = j + 1 := by simp [s7, s6, s5, s4, hs3_J]
  have hs7_W : s7 regLoopW = 2 ^ (r - j) := by simp [s7, s6, s5, s4, hs3_W]
  have hs7_N : s7 regLoopNode = node := by simp [s7, s6, s5, s4, hs3_S2]
  have hs7_S6 : s7 regS6 = w := by simp [s7, s6, s5, s4, hs3_S3]
  have hs7_VO : s7 regS7 = treeVertOff r j := by simp [s7, s6, s5, s4, hs3_VO]
  have hs7_V15 : s7 regV15 = netV15 n := by simp [s7, s6, s5, s4, hs3_V15]
  rcases rmMul_spec regS2 regS1 regLoopW regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp s7 hi7.reg₁_le (by rw [hs7_S1, hs7_W]; omega)
    with ⟨s8, hs8_S2, hs8_fr, hm8⟩
  have hs8_S2' : s8 regS2 = (j + 1) * 2 ^ (r - j) := by rw [hs8_S2, hs7_S1, hs7_W]
  have hs8_VO : s8 regS7 = treeVertOff r j := by
    rw [hs8_fr regS7 (by decide) (by decide) (by decide), hs7_VO]
  have ha9 := rmSetAdd_spec regLoopW regS7 regS2 (by decide) (by decide) (by decide)
    V inp s8 hm8.reg₁_le (by rw [hs8_VO, hs8_S2']; omega)
  set s9 := regUpd (regUpd s8 regLoopW (s8 regS7 + s8 regS2)) regS0 0
  have hs9_W : s9 regLoopW = treeVertOff r (j + 1) := by simp [s9, hs8_VO, hs8_S2', hvostep]
  have hs9_N : s9 regLoopNode = node := by
    dsimp only [s9]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
      hs8_fr regLoopNode (by decide) (by decide) (by decide), hs7_N]
  have hs9_S1 : s9 regS1 = j + 1 := by
    dsimp only [s9]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
      hs8_fr regS1 (by decide) (by decide) (by decide), hs7_S1]
  rcases rmMul_spec regS2 regLoopNode regS1 regS3 regS4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp s9 ha9.reg₁_le (by rw [hs9_N, hs9_S1]; omega)
    with ⟨s10, hs10_S2, hs10_fr, hm10⟩
  have hs10_S2' : s10 regS2 = node * (j + 1) := by rw [hs10_S2, hs9_N, hs9_S1]
  have hs10_VO : s10 regS7 = treeVertOff r j := by
    rw [hs10_fr regS7 (by decide) (by decide) (by decide)]; simp [s9, hs8_VO]
  have hs10_V15 : s10 regV15 = netV15 n := by
    rw [hs10_fr regV15 (by decide) (by decide) (by decide)]
    dsimp only [s9]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
      hs8_fr regV15 (by decide) (by decide) (by decide), hs7_V15]
  have ha11 := rmAdd_spec regS7 regV15 regS0 (by decide) (by decide) V inp s10 hm10.reg₁_le
    (by rw [hs10_VO, hs10_V15]; omega)
  set s11 := regUpd (regUpd s10 regS7 (s10 regS7 + s10 regV15)) regS0 0
  have hs11_S7 : s11 regS7 = netV15 n + treeVertOff r j := by simp [s11, hs10_VO, hs10_V15]; omega
  have hs11_S2 : s11 regS2 = node * (j + 1) := by simp [s11, hs10_S2']
  have ha12 := rmAdd_spec regS7 regS2 regS0 (by decide) (by decide) V inp s11 ha11.reg₁_le
    (by rw [hs11_S7, hs11_S2]; omega)
  set s12 := regUpd (regUpd s11 regS7 (s11 regS7 + s11 regS2)) regS0 0
  have hact_sa : ∀ a b c : Fin EncR, rmSetAdd a b c rmSetAddEntry ≠ none := by
    intros; simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]
  have hact_mul : ∀ a b c d e : Fin EncR, rmMul a b c d e rmMulEntry ≠ none := by
    intros; simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]
  have hcomb := rmChain_spec_inl (hact_sa _ _ _) ha1
    (rmChain_spec_inl (by simp [rmInc]) hi2
      (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd3
        (rmChain_spec_inl (by simp [rmCopy]) hc4
          (rmChain_spec_inl (by simp [rmCopy]) hc5
            (rmChain_spec_inl (by simp [rmCopy]) hc6
              (rmChain_spec_inl (by simp [rmInc]) hi7
                (rmChain_spec_inl (hact_mul _ _ _ _ _) hm8
                  (rmChain_spec_inl (hact_sa _ _ _) ha9
                    (rmChain_spec_inl (hact_mul _ _ _ _ _) hm10
                      (rmChain_spec_inl (by simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]) ha11 ha12))))))))))
  have hm8_le : (j + 1) * (2 * 2 ^ (r - j) + 3) ≤ 30 * n + 6 := by
    have : (j + 1) * (2 * 2 ^ (r - j) + 3) = 2 * ((j + 1) * 2 ^ (r - j)) + 3 * (j + 1) := by ring
    omega
  have hm10_le : node * (2 * (j + 1) + 3) ≤ 40 * n := by
    have h1 : node * (2 * (j + 1) + 3) = 2 * (node * (j + 1)) + 3 * node := by ring
    have h2 : 2 ^ (r - j) ≤ 2 * n := by
      calc 2 ^ (r - j) ≤ 2 ^ treeLog n := Nat.pow_le_pow_right (by decide) (by omega)
        _ = treeM n := rfl
        _ ≤ 2 * n := hM_le
    omega
  have hT : 2 * reg regLoopJ + 3 + (1 + (15 * s2 regLoopNode + 2 * s2 regS1 + 10 + (1 + (1 + (1 + (1 +
      (s7 regS1 * (2 * s7 regLoopW + 3) + 3 + (2 * s8 regS2 + 3 +
        (s9 regLoopNode * (2 * s9 regS1 + 3) + 3 + (2 * s10 regV15 + 2 + (2 * s11 regS2 + 2))))))))))) ≤
      2000 * n + 200 := by
    rw [hJ, hs2_N, hs2_S1, hs7_S1, hs7_W, hs8_S2', hs9_N, hs9_S1, hs10_V15, hs11_S2]
    dsimp only [r] at hblk_le hvo_next_le hvo_12 hvostep hnode_mul_le hm8_le hm10_le ⊢
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 2000 * n + 200) (by simp) hT
  simp only [List.nil_append] at hfin
  have hkeep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ →
      s12 k = reg k := by
    intro k hk
    have hne : ∀ q : Fin EncR, (41 ≤ q.val ∧ q.val ≤ 48) ∨ q = regLoopNode ∨ q = regLoopW → k ≠ q := by
      intro q hq heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl <;> rcases hq with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
    dsimp only [s12, s11]
    rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS7 (Or.inl (by decide))),
        regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS7 (Or.inl (by decide))),
        hs10_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))]
    dsimp only [s9]
    rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regLoopW (Or.inr (Or.inr rfl))),
        hs8_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))]
    dsimp only [s7, s6, s5, s4]
    rw [regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
        regUpd_ne _ (hne regS6 (Or.inl (by decide))), regUpd_ne _ (hne regLoopNode (Or.inr (Or.inl rfl))),
        hs3_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
          (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regS6 (Or.inl (by decide)))]
    dsimp only [s2, s1]
    rw [regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
        regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
  refine ⟨s12, fun k hk => hkeep k (Or.inl hk),
    hkeep regLoopI (Or.inr (Or.inl rfl)),
    hkeep regLoopRem (Or.inr (Or.inr (Or.inl rfl))),
    by rw [hkeep regLoopJ (Or.inr (Or.inr (Or.inr rfl))), hJ],
    ?_, ?_, ?_, by simp [s12, hs11_S7, hs11_S2], hfin⟩
  · dsimp only [s12, s11]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        hs10_fr regLoopNode (by decide) (by decide) (by decide), hs9_N]
  · dsimp only [s12, s11]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        hs10_fr regS6 (by decide) (by decide) (by decide)]
    dsimp only [s9]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        hs8_fr regS6 (by decide) (by decide) (by decide), hs7_S6]
  · dsimp only [s12, s11]
    rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide), regUpd_ne _ (by decide),
        hs10_fr regLoopW (by decide) (by decide) (by decide), hs9_W]

/-- Full B12 decoder: runs init + `rmB12Test` + `rmWhile rmB12Step` + `rmB12Fin`. -/
abbrev RMB12WhileQ : Type := Option Bool ⊕ (Unit ⊕ (Bool ⊕ RMB12StepQ))
abbrev RMB12DecodeQ : Type :=
  RMSetConstQ 1 ⊕ (Bool ⊕ (Bool ⊕ (Bool ⊕ (RMB12TestQ ⊕ (RMB12WhileQ ⊕ RMB12FinQ)))))

def rmB12Decode : RMProg EncR RMB12DecodeQ :=
  rmChain (rmSetConst regLoopJ 1)
    (rmChain (rmCopy regLoopNode regLoopI)
      (rmChain (rmCopy regLoopW regTreeM)
        (rmChain (rmZero regS7)
          (rmChain rmB12Test
            (rmChain (rmWhile regS0 rmB12Step rmB12StepEntry) rmB12Fin rmB12FinEntry)
            (Sum.inl rmWhileEntry))
          (Sum.inl rmB12TestEntry))
        (Sum.inl false))
      (Sum.inl false))
    (Sum.inl false)

def rmB12DecodeEntry : RMB12DecodeQ := Sum.inl rmSetConstEntry
def rmB12DecodeExit : RMB12DecodeQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmB12FinExit)))))

lemma rmB12Decode_spec (n V : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hI : reg regLoopI < treeEdgeOff (treeLog n + 1) (treeLog n + 2)) :
    let r := treeLog n + 1
    let t := decodeTreeEdge r (reg regLoopI)
    ∃ r1 : RegState EncR,
      PreservedRegs r1 reg ∧
      r1 regLoopI = reg regLoopI ∧
      r1 regLoopRem = reg regLoopRem ∧
      1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < 2 * t.1 + 1 ∧
      r1 regLoopJ = t.1 ∧
      r1 regLoopNode = t.2.1 ∧
      r1 regS6 = t.2.2 ∧
      r1 regLoopW = treeVertOff r (t.1 + 1) ∧
      r1 regS7 = netV15 n + treeVertOff r t.1 + t.2.1 * (t.1 + 1) ∧
      RMExec rmB12Decode V inp rmB12DecodeEntry reg rmB12DecodeExit r1 [] (300 * n ^ 2 + 2500 * n + 400) := by
  intro r t
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hTM : reg regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  set locE := reg regLoopI
  have hs1 := rmSetConst_spec regLoopJ 1 V inp reg hreg (by omega)
  set r1 := regUpd reg regLoopJ 1
  have hc2 := rmCopy_spec regLoopNode regLoopI V inp r1 hs1.reg₁_le
  set r2 := regUpd r1 regLoopNode (r1 regLoopI)
  have hc3 := rmCopy_spec regLoopW regTreeM V inp r2 hc2.reg₁_le
  set r3 := regUpd r2 regLoopW (r2 regTreeM)
  have hz4 := rmZero_spec regS7 V inp r3 hc3.reg₁_le
  set r4 := regUpd r3 regS7 0
  have h4_J : r4 regLoopJ = 1 := by simp [r4, r3, r2, r1]
  have h4_N : r4 regLoopNode = locE := by simp [r4, r3, r2, r1, locE]
  have h4_W : r4 regLoopW = 2 ^ (r - 1) := by
    have : r - 1 = treeLog n := by omega
    rw [this]; simp [r4, r3, r2, r1, hTM, treeM]
  have h4_VO : r4 regS7 = treeVertOff r 1 := by simp [r4, treeVertOff]
  have h4_pr : PreservedRegs r4 reg :=
    (PreservedRegs.upd_ge _ regS7 _ (by decide)).trans
      ((PreservedRegs.upd_ge _ regLoopW _ (by decide)).trans
        ((PreservedRegs.upd_ge _ regLoopNode _ (by decide)).trans
          (PreservedRegs.upd_ge _ regLoopJ _ (by decide))))
  rcases rmB12Test_spec n V 1 locE inp r4 hn hz4.reg₁_le hV (le_refl 1) (by omega) h4_J h4_N h4_W
    with ⟨r5, h5_S5, h5_S0, h5_fr, ht5⟩
  have h5_pr : PreservedRegs r5 reg := fun k hk => by
    have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
      have := congrArg Fin.val heq; omega
    rw [h5_fr k (hne regS0 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide))
        (hne regS3 (by decide)) (hne regS5 (by decide)), h4_pr k hk]
  rcases rmB12While_spec n V inp hn hV r 1 locE r5 (le_refl 1) (by omega)
      (by simpa [treeEdgeOff] using hI) ht5.reg₁_le
      (by rw [h5_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide), h4_J])
      (by rw [h5_fr regLoopNode (by decide) (by decide) (by decide) (by decide) (by decide), h4_N])
      (by rw [h5_fr regLoopW (by decide) (by decide) (by decide) (by decide) (by decide), h4_W])
      (by rw [h5_fr regS7 (by decide) (by decide) (by decide) (by decide) (by decide), h4_VO])
      h5_S5 h5_S0
    with ⟨r6, ht1, htr, h6J, h6Nlt, h6div, h6mod, h6W, h6VO, h6pr, h6I, h6rem, hw6⟩
  have ht_eq : decodeTreeEdgeAux (treeLog n + 1) locE r 1 = t := rfl
  rw [ht_eq] at ht1 htr h6J h6Nlt h6div h6mod h6W h6VO
  have hp6 := hp.of_preserved (h6pr.trans h5_pr)
  rcases rmB12Fin_spec n V t.1 (r6 regLoopNode) inp r6 hn hp6 hw6.reg₁_le hV
      ht1 htr h6J rfl h6Nlt h6W h6VO
    with ⟨r7, h7pr, h7I, h7rem, h7J, h7N, h7S6, h7W, h7S7, hf7⟩
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hs1
    (rmChain_spec_inl (by simp [rmCopy]) hc2
      (rmChain_spec_inl (by simp [rmCopy]) hc3
        (rmChain_spec_inl (by simp [rmZero]) hz4
          (rmChain_spec_inl (by simp [rmB12Test, rmB12TestEntry, rmChain, rmSeq, rmSetAdd, rmSetAddEntry, rmCopy]) ht5
            (rmChain_spec_inl (by simp [rmWhile, rmWhileEntry, rmLoop, rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]) hw6 hf7)))))
  have hT : 1 + 1 + (1 + (1 + (1 + (100 * n + 30 + (r * (260 * n + 82) + 2 + (2000 * n + 200)))))) ≤
      300 * n ^ 2 + 2500 * n + 400 := by
    have hmul : r * (260 * n + 82) ≤ (n + 1) * (260 * n + 82) := Nat.mul_le_mul_right _ (by omega)
    have hring : (n + 1) * (260 * n + 82) = 260 * n ^ 2 + 342 * n + 82 := by ring
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 300 * n ^ 2 + 2500 * n + 400) (by simp) hT
  simp only [List.nil_append] at hfin
  have h5_I : r5 regLoopI = reg regLoopI := by
    rw [h5_fr regLoopI (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, r3, r2, r1]
  have h5_rem : r5 regLoopRem = reg regLoopRem := by
    rw [h5_fr regLoopRem (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, r3, r2, r1]
  refine ⟨r7, h7pr.trans (h6pr.trans h5_pr), by rw [h7I, h6I, h5_I], by rw [h7rem, h6rem, h5_rem],
    ht1, htr, by rw [← h6div]; exact Nat.div_lt_of_lt_mul h6Nlt,
    by rw [← h6mod]; exact Nat.mod_lt _ (by omega),
    h7J, by rw [h7N, h6div], by rw [h7S6, h6mod], h7W, by rw [h7S7, h6div], hfin⟩

/-- B12 `src` (`regEndU`) emitter given `regS6 = w`, `regS7 = baseSrc`. -/
abbrev RMB12SrcNzQ : Type := Bool ⊕ (Bool ⊕ (RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ Bool))))
abbrev RMB12SrcQ : Type := Option Bool ⊕ (Bool ⊕ (Bool ⊕ RMB12SrcNzQ))

def rmB12SrcNz : RMProg EncR RMB12SrcNzQ :=
  rmChain (rmCopy regS1 regS6)
    (rmChain (rmDec1 regS1)
      (rmChain (rmSetConst regS2 2)
        (rmChain (rmDivMod regS3 regS4 regS1 regS2 regS0 regS5 regEndV)
          (rmChain (rmSetAdd regEndU regS7 regS3) (rmInc regEndU) false)
          (Sum.inl rmSetAddEntry))
        (Sum.inl rmDivModEntry))
      (Sum.inl rmSetConstEntry))
    (Sum.inl false)

def rmB12Src : RMProg EncR RMB12SrcQ :=
  rmIfZero regS6 (rmCopy regEndU regS7) rmB12SrcNz false (Sum.inl false)

lemma rmB12Src_spec (n V j node w : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hw : w < 2 * j + 1)
    (hS6 : reg regS6 = w)
    (hS7 : reg regS7 = netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1)) :
    ∃ q₁ r1,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
        k = regLoopNode ∨ k = regLoopW ∨ k = regS6 ∨ k = regS7 → r1 k = reg k) ∧
      r1 regEndU = (if w = 0 then netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1)
                    else netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1) + 1 + (w - 1) / 2) ∧
      RMExec rmB12Src V inp rmIfZeroEntry reg q₁ r1 [] (100 * n + 50) := by
  set r := treeLog n + 1
  have h1V : 1 ≤ V := by omega
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
    simpa [r] using netV15_add_treeVertOff_le n
  have hvo_next : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) :=
    treeVertOff_step hj1
  have hvo_mono : treeVertOff r (j + 1) ≤ treeVertOff r (r + 1) := treeVertOff_mono r (by omega)
  have hnode_bd : (node + 1) * (j + 1) ≤ (j + 1) * 2 ^ (r - j) := by
    calc (node + 1) * (j + 1) ≤ 2 ^ (r - j) * (j + 1) := Nat.mul_le_mul_right _ hnode
      _ = (j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  have hlin : (node + 1) * (j + 1) = node * (j + 1) + (j + 1) := by ring
  by_cases hw0 : w = 0
  · have hcp := rmCopy_spec regEndU regS7 V inp reg hreg
    have hif := (rmIfZero_zero_spec regS6 rmB12SrcNz (Sum.inl false) (by rw [hS6, hw0]) hcp).weaken
      (V₂ := V) (T₂ := 100 * n + 50) (le_refl _) (by omega)
    refine ⟨_, _, ?_, by simp [hw0, hS7], hif⟩
    intro k hk
    have hne : k ≠ regEndU := fun heq => by
      have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp at hv); omega
    exact regUpd_ne reg hne _
  · have hc1 := rmCopy_spec regS1 regS6 V inp reg hreg
    set s1 := regUpd reg regS1 (reg regS6)
    have hd2 := rmDec1_spec regS1 V inp s1 hc1.reg₁_le
    set s2 := regUpd s1 regS1 (s1 regS1 - 1)
    have hsc3 := rmSetConst_spec regS2 2 V inp s2 hd2.reg₁_le (by omega)
    set s3 := regUpd s2 regS2 2
    have hs3_S1 : s3 regS1 = w - 1 := by simp [s3, s2, s1, hS6]
    have hs3_S2 : s3 regS2 = 2 := by simp [s3]
    rcases rmDivMod_spec regS3 regS4 regS1 regS2 regS0 regS5 regEndV
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        V inp s3 (by rw [hs3_S2]; decide) hsc3.reg₁_le h1V
      with ⟨s4, hs4_q, _, hs4_fr, hd4⟩
    have hs4_S3 : s4 regS3 = (w - 1) / 2 := by rw [hs4_q, hs3_S1, hs3_S2]
    have hs4_S7 : s4 regS7 = netV15 n + treeVertOff r j + node * (j + 1) := by
      rw [hs4_fr regS7 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [s3, s2, s1, hS7]
    have ha5 := rmSetAdd_spec regEndU regS7 regS3 (by decide) (by decide) (by decide)
      V inp s4 hd4.reg₁_le (by rw [hs4_S7, hs4_S3]; omega)
    set s5 := regUpd (regUpd s4 regEndU (s4 regS7 + s4 regS3)) regS0 0
    have hi6 := rmInc_spec regEndU V inp s5 ha5.reg₁_le (by simp [s5, hs4_S7, hs4_S3]; omega)
    set s6 := regUpd s5 regEndU (s5 regEndU + 1)
    have hnz := rmChain_spec_inl (by simp [rmCopy]) hc1
      (rmChain_spec_inl (by simp [rmDec1]) hd2
        (rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc3
          (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd4
            (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha5 hi6))))
    have hT : 2 + (1 + (1 + (1 + 2 + (15 * s3 regS1 + 2 * s3 regS2 + 10 + (2 * s4 regS3 + 3 + 1))))) ≤
        100 * n + 50 := by
      rw [hs3_S1, hs3_S2, hs4_S3]; omega
    have hif := (rmIfZero_pos_spec regS6 (rmCopy regEndU regS7) false (by rw [hS6]; exact hw0) hnz).weaken
      (V₂ := V) (T₂ := 100 * n + 50) (by simp) hT
    simp only [List.nil_append] at hif
    refine ⟨_, s6, ?_, by simp [s6, s5, hs4_S7, hs4_S3, hw0]; omega, hif⟩
    intro k hk
    have hne : ∀ q : Fin EncR, (41 ≤ q.val ∧ q.val ≤ 46) ∨ q = regEndU ∨ q = regEndV → k ≠ q := by
      intro q hq heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with ⟨h1, h2⟩ | rfl | rfl <;> (try simp at hv) <;> omega
    dsimp only [s6, s5]
    rw [regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl))), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
        regUpd_ne _ (hne regEndU (Or.inr (Or.inl rfl))),
        hs4_fr k (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))
          (hne regS0 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regEndV (Or.inr (Or.inr rfl)))]
    dsimp only [s3, s2, s1]
    rw [regUpd_ne _ (hne regS2 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
        regUpd_ne _ (hne regS1 (Or.inl (by decide)))]

/-- B12 `dst` (`regEndV`) parent-branch helper (`j < r`). -/
abbrev RMB12DstParentQ : Type :=
  RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (Bool ⊕ (Fin 3 ⊕ (RMMulQ ⊕ (RMSetAddQ ⊕ (RMAddQ ⊕ (Bool ⊕ RMAddQ)))))))

def rmB12DstParent : RMProg EncR RMB12DstParentQ :=
  rmChain (rmSetConst regS1 2)
    (rmChain (rmDivMod regS3 regS4 regLoopNode regS1 regS0 regS5 regEndV)
      (rmChain (rmCopy regS1 regLoopJ)
        (rmChain (rmAddConst regS1 2)
          (rmChain (rmMul regS4 regS3 regS1 regS0 regS5)
            (rmChain (rmSetAdd regEndV regV15 regLoopW)
              (rmChain (rmAdd regEndV regS4 regS0)
                (rmChain (rmInc regEndV) (rmAdd regEndV regS2 regS0) rmAddEntry)
                (Sum.inl false))
              (Sum.inl rmAddEntry))
            (Sum.inl rmSetAddEntry))
          (Sum.inl rmMulEntry))
        (Sum.inl ⟨0, by omega⟩))
      (Sum.inl false))
    (Sum.inl rmDivModEntry)

def rmB12DstParentEntry : RMB12DstParentQ := Sum.inl rmSetConstEntry
def rmB12DstParentExit : RMB12DstParentQ :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr rmAddExit)))))))

lemma rmB12DstParent_spec (n V j node w : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j < treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hw : w < 2 * j + 1)
    (hJ : reg regLoopJ = j) (hN : reg regLoopNode = node)
    (hS2 : reg regS2 = w / 2) (hW : reg regLoopW = treeVertOff (treeLog n + 1) (j + 1)) :
    ∃ r1 : RegState EncR,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → r1 k = reg k) ∧
      r1 regEndV = netV15 n + treeVertOff (treeLog n + 1) (j + 1) + (node / 2) * (j + 2) + 1 + w / 2 ∧
      RMExec rmB12DstParent V inp rmB12DstParentEntry reg rmB12DstParentExit r1 [] (200 * n + 80) := by
  set r := treeLog n + 1
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
    simpa [r] using netV15_add_treeVertOff_le n
  have hvo_step2 : treeVertOff r (j + 2) = treeVertOff r (j + 1) + (j + 2) * 2 ^ (r - (j + 1)) :=
    treeVertOff_step (by omega)
  have hvo_mono2 : treeVertOff r (j + 2) ≤ treeVertOff r (r + 1) := treeVertOff_mono r (by omega)
  have hvo_12 : treeVertOff r (r + 1) ≤ 12 * n := by
    have hr1 : r + 1 = treeLog n + 2 := by omega
    rw [hr1, treeVertOff_net]; omega
  have hnode_div_lt : node / 2 < 2 ^ (r - (j + 1)) := by
    have hexp : 2 ^ (r - j) = 2 * 2 ^ (r - (j + 1)) := by
      have : r - j = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']
    rw [hexp] at hnode; exact Nat.div_lt_of_lt_mul hnode
  have hnode_le_2n : node ≤ 2 * n := by
    have : 2 ^ (r - j) ≤ 2 * n := by
      calc 2 ^ (r - j) ≤ 2 ^ treeLog n := Nat.pow_le_pow_right (by decide) (by omega)
        _ = treeM n := rfl
        _ ≤ 2 * n := hM_le
    omega
  have hpar_bd : (node / 2 + 1) * (j + 2) ≤ (j + 2) * 2 ^ (r - (j + 1)) := by
    calc (node / 2 + 1) * (j + 2) ≤ 2 ^ (r - (j + 1)) * (j + 2) := Nat.mul_le_mul_right _ hnode_div_lt
      _ = (j + 2) * 2 ^ (r - (j + 1)) := Nat.mul_comm _ _
  have hlin : (node / 2 + 1) * (j + 2) = (node / 2) * (j + 2) + (j + 2) := by ring
  have hV15 : reg regV15 = netV15 n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsc1 := rmSetConst_spec regS1 2 V inp reg hreg (by omega)
  set s1 := regUpd reg regS1 2
  have hs1_N : s1 regLoopNode = node := by simp [s1, hN]
  rcases rmDivMod_spec regS3 regS4 regLoopNode regS1 regS0 regS5 regEndV
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      V inp s1 (by simp [s1]) hsc1.reg₁_le h1V
    with ⟨s2, hs2_q, _, hs2_fr, hd2⟩
  have hs2_S3 : s2 regS3 = node / 2 := by rw [hs2_q, hs1_N]; simp [s1]
  have hs2_J : s2 regLoopJ = j := by
    rw [hs2_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hJ]
  have hs2_S2 : s2 regS2 = w / 2 := by
    rw [hs2_fr regS2 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hS2]
  have hs2_W : s2 regLoopW = treeVertOff r (j + 1) := by
    rw [hs2_fr regLoopW (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hW]
  have hs2_V15 : s2 regV15 = netV15 n := by
    rw [hs2_fr regV15 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hV15]
  have hc3 := rmCopy_spec regS1 regLoopJ V inp s2 hd2.reg₁_le
  set s3 := regUpd s2 regS1 (s2 regLoopJ)
  have ha4 := rmAddConst_spec regS1 2 V inp s3 hc3.reg₁_le (by simp [s3, hs2_J]; omega)
  set s4 := regUpd s3 regS1 (s3 regS1 + 2)
  have hs4_S1 : s4 regS1 = j + 2 := by simp [s4, s3, hs2_J]
  have hs4_S3 : s4 regS3 = node / 2 := by simp [s4, s3, hs2_S3]
  rcases rmMul_spec regS4 regS3 regS1 regS0 regS5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      V inp s4 ha4.reg₁_le (by rw [hs4_S3, hs4_S1]; omega)
    with ⟨s5, hs5_S4, hs5_fr, hm5⟩
  have hs5_S4' : s5 regS4 = (node / 2) * (j + 2) := by rw [hs5_S4, hs4_S3, hs4_S1]
  have hs5_V15 : s5 regV15 = netV15 n := by
    rw [hs5_fr regV15 (by decide) (by decide) (by decide)]; simp [s4, s3, hs2_V15]
  have hs5_W : s5 regLoopW = treeVertOff r (j + 1) := by
    rw [hs5_fr regLoopW (by decide) (by decide) (by decide)]; simp [s4, s3, hs2_W]
  have hs5_S2 : s5 regS2 = w / 2 := by
    rw [hs5_fr regS2 (by decide) (by decide) (by decide)]; simp [s4, s3, hs2_S2]
  have ha6 := rmSetAdd_spec regEndV regV15 regLoopW (by decide) (by decide) (by decide)
    V inp s5 hm5.reg₁_le (by rw [hs5_V15, hs5_W]; omega)
  set s6 := regUpd (regUpd s5 regEndV (s5 regV15 + s5 regLoopW)) regS0 0
  have hs6_V : s6 regEndV = netV15 n + treeVertOff r (j + 1) := by simp [s6, hs5_V15, hs5_W]
  have hs6_S4 : s6 regS4 = (node / 2) * (j + 2) := by simp [s6, hs5_S4']
  have ha7 := rmAdd_spec regEndV regS4 regS0 (by decide) (by decide) V inp s6 ha6.reg₁_le
    (by rw [hs6_V, hs6_S4]; omega)
  set s7 := regUpd (regUpd s6 regEndV (s6 regEndV + s6 regS4)) regS0 0
  have hs7_V : s7 regEndV = netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) := by
    simp [s7, hs6_V, hs6_S4]
  have hi8 := rmInc_spec regEndV V inp s7 ha7.reg₁_le (by rw [hs7_V]; omega)
  set s8 := regUpd s7 regEndV (s7 regEndV + 1)
  have hs8_V : s8 regEndV = netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) + 1 := by
    simp [s8, hs7_V]
  have hs8_S2 : s8 regS2 = w / 2 := by simp [s8, s7, s6, hs5_S2]
  have ha9 := rmAdd_spec regEndV regS2 regS0 (by decide) (by decide) V inp s8 hi8.reg₁_le
    (by rw [hs8_V, hs8_S2]; omega)
  set s9 := regUpd (regUpd s8 regEndV (s8 regEndV + s8 regS2)) regS0 0
  have hact_add : ∀ a b c : Fin EncR, rmAdd a b c rmAddEntry ≠ none := by
    intros; simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc1
    (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd2
      (rmChain_spec_inl (by simp [rmCopy]) hc3
        (rmChain_spec_inl (by simp [rmAddConst]) ha4
          (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hm5
            (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha6
              (rmChain_spec_inl (hact_add _ _ _) ha7
                (rmChain_spec_inl (by simp [rmInc]) hi8 ha9)))))))
  have hmul_le : (node / 2) * (2 * (j + 2) + 3) ≤ 40 * n := by
    have : (node / 2) * (2 * (j + 2) + 3) = 2 * ((node / 2) * (j + 2)) + 3 * (node / 2) := by ring
    omega
  have hT : 1 + 2 + (15 * s1 regLoopNode + 2 * s1 regS1 + 10 + (1 + (2 +
      (s4 regS3 * (2 * s4 regS1 + 3) + 3 + (2 * s5 regLoopW + 3 +
        (2 * s6 regS4 + 2 + (1 + (2 * s8 regS2 + 2)))))))) ≤ 200 * n + 80 := by
    have hs1S1 : s1 regS1 = 2 := by simp [s1]
    rw [hs1_N, hs1S1, hs4_S3, hs4_S1, hs5_W, hs6_S4, hs8_S2]; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 200 * n + 80) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨s9, ?_, by simp [s9, hs8_V, hs8_S2], hfin⟩
  intro k hk
  have hne : ∀ q : Fin EncR, (41 ≤ q.val ∧ q.val ≤ 46) ∨ q = regEndV → k ≠ q := by
    intro q hq heq; have hv := congrArg Fin.val heq
    rcases hk with hk | rfl | rfl | rfl <;> rcases hq with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
  dsimp only [s9, s8, s7, s6]
  rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regEndV (Or.inr rfl)),
      regUpd_ne _ (hne regEndV (Or.inr rfl)), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
      regUpd_ne _ (hne regEndV (Or.inr rfl)), regUpd_ne _ (hne regS0 (Or.inl (by decide))),
      regUpd_ne _ (hne regEndV (Or.inr rfl)),
      hs5_fr k (hne regS4 (Or.inl (by decide))) (hne regS0 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
  dsimp only [s4, s3]
  rw [regUpd_ne _ (hne regS1 (Or.inl (by decide))), regUpd_ne _ (hne regS1 (Or.inl (by decide))),
      hs2_fr k (hne regS3 (Or.inl (by decide))) (hne regS4 (Or.inl (by decide)))
        (hne regS0 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regEndV (Or.inr rfl))]
  dsimp only [s1]; rw [regUpd_ne _ (hne regS1 (Or.inl (by decide)))]

/-- Full B12 `dst` (`regEndV`) emitter. -/
abbrev RMB12DstElseQ : Type :=
  Bool ⊕ (Bool ⊕ (Fin 8 ⊕ (Option Bool ⊕ (RMSetAddQ ⊕ (Bool ⊕ RMB12DstParentQ)))))
abbrev RMB12DstThenQ : Type := RMSetAddQ ⊕ Bool
abbrev RMB12DstQ : Type :=
  RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (RMSetAddQ ⊕ (Fin 8 ⊕
    ((Option Bool ⊕ (Unit ⊕ (Bool ⊕ Bool))) ⊕
      (Option Bool ⊕ (RMB12DstElseQ ⊕ (Bool ⊕ RMB12DstThenQ)))))))

def rmB12DstElse : RMProg EncR RMB12DstElseQ :=
  rmChain (rmCopy regS1 regTreeLog)
    (rmChain (rmInc regS1)
      (rmChain (rmCmpLt regS0 regLoopJ regS1 regS3 regS4)
        (rmIfZero regS0 (rmSetAdd regEndV regV17 regS2) rmB12DstParent rmSetAddEntry rmB12DstParentEntry)
        rmIfZeroEntry)
      (Sum.inl 0))
    (Sum.inl false)

def rmB12DstThen : RMProg EncR RMB12DstThenQ :=
  rmChain (rmSetAdd regEndV regS7 regS2) (rmInc regEndV) false

def rmB12Dst : RMProg EncR RMB12DstQ :=
  rmChain (rmSetConst regS1 2)
    (rmChain (rmDivMod regS2 regS3 regS6 regS1 regS4 regS5 regEndV)
      (rmChain (rmSetAdd regS4 regLoopJ regLoopJ)
        (rmChain (rmCmpLt regS0 regS6 regS4 regS1 regS5)
          (rmChain (rmIfZero regS3 rmNop (rmZero regS0) () false)
            (rmIfZero regS0 rmB12DstElse rmB12DstThen (Sum.inl false) (Sum.inl rmSetAddEntry))
            rmIfZeroEntry)
          (Sum.inl rmIfZeroEntry))
        (Sum.inl 0))
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmDivModEntry)

def rmB12DstEntry : RMB12DstQ := Sum.inl rmSetConstEntry

lemma rmB12Dst_spec (n V j node w : ℕ) (inp : List Bool) (reg : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg) (hreg : ∀ i, reg i ≤ V) (hV : 500 * n + 20 ≤ V)
    (hj1 : 1 ≤ j) (hjr : j ≤ treeLog n + 1)
    (hnode : node < 2 ^ (treeLog n + 1 - j)) (hw : w < 2 * j + 1)
    (hJ : reg regLoopJ = j) (hN : reg regLoopNode = node)
    (hS6 : reg regS6 = w) (hW : reg regLoopW = treeVertOff (treeLog n + 1) (j + 1))
    (hS7 : reg regS7 = netV15 n + treeVertOff (treeLog n + 1) j + node * (j + 1)) :
    let r := treeLog n + 1
    ∃ q₁ r1,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → r1 k = reg k) ∧
      r1 regEndV =
        (if w % 2 = 0 ∧ w < 2 * j then
          netV15 n + treeVertOff r j + node * (j + 1) + 1 + w / 2
         else if j < r then
          netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) + 1 + w / 2
         else
          netV17 n + w / 2) ∧
      RMExec rmB12Dst V inp rmB12DstEntry reg q₁ r1 [] (300 * n + 150) := by
  intro r
  have h1V : 1 ≤ V := by omega
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
    simpa [r] using netV15_add_treeVertOff_le n
  have hv18_le : netV17 n + (treeLog n + 2) ≤ netVertCount n := by
    simp only [netVertCount, netV18]; omega
  have hvo_step : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := treeVertOff_step hj1
  have hvo_mono : treeVertOff r (j + 1) ≤ treeVertOff r (r + 1) := treeVertOff_mono r (by omega)
  have hnode_bd : (node + 1) * (j + 1) ≤ (j + 1) * 2 ^ (r - j) := by
    calc (node + 1) * (j + 1) ≤ 2 ^ (r - j) * (j + 1) := Nat.mul_le_mul_right _ hnode
      _ = (j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  have hlin : (node + 1) * (j + 1) = node * (j + 1) + (j + 1) := by ring
  have hsc1 := rmSetConst_spec regS1 2 V inp reg hreg (by omega)
  set s1 := regUpd reg regS1 2
  have hs1_S6 : s1 regS6 = w := by simp [s1, hS6]
  rcases rmDivMod_spec regS2 regS3 regS6 regS1 regS4 regS5 regEndV
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      V inp s1 (by simp [s1]) hsc1.reg₁_le h1V
    with ⟨s2, hs2_q, hs2_r, hs2_fr, hd2⟩
  have hs2_S2 : s2 regS2 = w / 2 := by rw [hs2_q, hs1_S6]; simp [s1]
  have hs2_S3 : s2 regS3 = w % 2 := by rw [hs2_r, hs1_S6]; simp [s1]
  have hs2_J : s2 regLoopJ = j := by
    rw [hs2_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [s1, hJ]
  have hs2_S6 : s2 regS6 = w := by
    rw [hs2_fr regS6 (by decide) (by decide) (by decide) (by decide) (by decide), hs1_S6]
  have ha3 := rmSetAdd_spec regS4 regLoopJ regLoopJ (by decide) (by decide) (by decide)
    V inp s2 hd2.reg₁_le (by rw [hs2_J]; omega)
  set s3 := regUpd (regUpd s2 regS4 (s2 regLoopJ + s2 regLoopJ)) regS0 0
  have hs3_S6 : s3 regS6 = w := by simp [s3, hs2_S6]
  have hs3_S4 : s3 regS4 = 2 * j := by simp [s3, hs2_J]; omega
  rcases rmCmpLt_spec regS0 regS6 regS4 regS1 regS5 (by decide) (by decide) (by decide) (by decide)
      V inp s3 ha3.reg₁_le h1V with ⟨s4, hs4_fl, hs4_fr, hcmp4⟩
  have hs4_S3 : s4 regS3 = w % 2 := by
    rw [hs4_fr regS3 (by decide) (by decide) (by decide)]; simp [s3, hs2_S3]
  have hs4_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
      k = regLoopNode ∨ k = regLoopW ∨ k = regEndU ∨ k = regS7 → s4 k = reg k := by
    intro k hk
    have hne : ∀ q : Fin EncR, (41 ≤ q.val ∧ q.val ≤ 46) ∨ q = regEndV → k ≠ q := by
      intro q hq heq; have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with ⟨h1, h2⟩ | rfl <;> (try simp at hv) <;> omega
    rw [hs4_fr k (hne regS0 (Or.inl (by decide))) (hne regS1 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide)))]
    dsimp only [s3]
    rw [regUpd_ne _ (hne regS0 (Or.inl (by decide))), regUpd_ne _ (hne regS4 (Or.inl (by decide))),
        hs2_fr k (hne regS2 (Or.inl (by decide))) (hne regS3 (Or.inl (by decide)))
          (hne regS4 (Or.inl (by decide))) (hne regS5 (Or.inl (by decide))) (hne regEndV (Or.inr rfl))]
    dsimp only [s1]; rw [regUpd_ne _ (hne regS1 (Or.inl (by decide)))]
  have hs4_S2 : s4 regS2 = w / 2 := by
    rw [hs4_fr regS2 (by decide) (by decide) (by decide)]; simp [s3, hs2_S2]
  have hmask : ∃ qM s5,
      s5 regS0 = (if w % 2 = 0 ∧ w < 2 * j then 1 else 0) ∧
      (∀ k : Fin EncR, k ≠ regS0 → s5 k = s4 k) ∧
      RMExec (rmIfZero regS3 rmNop (rmZero regS0) () false) V inp rmIfZeroEntry s4 qM s5 [] 3 := by
    by_cases hmod : w % 2 = 0
    · have h0 := (rmIfZero_zero_spec regS3 (rmZero regS0) false (by rw [hs4_S3, hmod])
        (rmNop_spec V inp s4 hcmp4.reg₁_le)).weaken (V₂ := V) (T₂ := 3) (le_refl _) (by omega)
      refine ⟨_, s4, ?_, fun _ _ => rfl, h0⟩
      rw [hs4_fl, hs3_S6, hs3_S4]; simp [hmod]
    · have hz := rmZero_spec regS0 V inp s4 hcmp4.reg₁_le
      have h1 := rmIfZero_pos_spec regS3 rmNop () (by rw [hs4_S3]; exact hmod) hz
      refine ⟨_, regUpd s4 regS0 0, by simp [hmod], fun k hk => regUpd_ne s4 hk 0, h1⟩
  rcases hmask with ⟨qM, s5, hs5_fl, hs5_fr, hif5⟩
  have hs5_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
      k = regLoopNode ∨ k = regLoopW ∨ k = regEndU ∨ k = regS7 → s5 k = reg k := fun k hk => by
    have hne : k ≠ regS0 := fun heq => by
      have hv := congrArg Fin.val heq
      rcases hk with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp at hv); omega
    rw [hs5_fr k hne, hs4_keep k hk]
  have hs5_S2 : s5 regS2 = w / 2 := by rw [hs5_fr regS2 (by decide), hs4_S2]
  have hs5_S7 : s5 regS7 = netV15 n + treeVertOff r j + node * (j + 1) := by
    rw [hs5_keep regS7 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))), hS7]
  have hbr : ∃ qB s6,
      (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → s6 k = s5 k) ∧
      s6 regEndV =
        (if w % 2 = 0 ∧ w < 2 * j then
          netV15 n + treeVertOff r j + node * (j + 1) + 1 + w / 2
         else if j < r then
          netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) + 1 + w / 2
         else
          netV17 n + w / 2) ∧
      RMExec (rmIfZero regS0 rmB12DstElse rmB12DstThen (Sum.inl false) (Sum.inl rmSetAddEntry))
        V inp rmIfZeroEntry s5 qB s6 [] (220 * n + 100) := by
    by_cases hcond : w % 2 = 0 ∧ w < 2 * j
    · have hfl : s5 regS0 ≠ 0 := by rw [hs5_fl]; simp [hcond]
      have ha1 := rmSetAdd_spec regEndV regS7 regS2 (by decide) (by decide) (by decide)
        V inp s5 hif5.reg₁_le (by rw [hs5_S7, hs5_S2]; omega)
      set t1 := regUpd (regUpd s5 regEndV (s5 regS7 + s5 regS2)) regS0 0
      have hi2 := rmInc_spec regEndV V inp t1 ha1.reg₁_le (by simp [t1, hs5_S7, hs5_S2]; omega)
      set t2 := regUpd t1 regEndV (t1 regEndV + 1)
      have hth := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha1 hi2
      have hif := (rmIfZero_pos_spec regS0 rmB12DstElse (Sum.inl false) hfl hth).weaken
        (V₂ := V) (T₂ := 220 * n + 100) (by simp) (by rw [hs5_S2]; omega)
      simp only [List.nil_append] at hif
      refine ⟨_, t2, ?_, by simp [t2, t1, hcond, hs5_S7, hs5_S2]; omega, hif⟩
      intro k hk
      have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regEndV → k ≠ q := by
        intro q hq heq; have hv := congrArg Fin.val heq
        rcases hk with hk | rfl | rfl | rfl <;> rcases hq with rfl | rfl <;> (try simp at hv) <;> omega
      dsimp only [t2, t1]
      rw [regUpd_ne _ (hne regEndV (Or.inr rfl)), regUpd_ne _ (hne regS0 (Or.inl rfl)),
          regUpd_ne _ (hne regEndV (Or.inr rfl))]
    · have hfl : s5 regS0 = 0 := by rw [hs5_fl]; simp [hcond]
      have hp5 := hp.of_preserved (fun k hk => hs5_keep k (Or.inl hk))
      have h5_TL : s5 regTreeLog = treeLog n := hp5.2.2.2.2.2.2.2.2.2.2.1
      have h5_J : s5 regLoopJ = j := by
        rw [hs5_keep regLoopJ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hJ]
      have hc1 := rmCopy_spec regS1 regTreeLog V inp s5 hif5.reg₁_le
      set t1 := regUpd s5 regS1 (s5 regTreeLog)
      have hi2 := rmInc_spec regS1 V inp t1 hc1.reg₁_le (by simp [t1, h5_TL]; omega)
      set t2 := regUpd t1 regS1 (t1 regS1 + 1)
      have ht2_S1 : t2 regS1 = r := by simp [t2, t1, h5_TL, r]
      have ht2_J : t2 regLoopJ = j := by simp [t2, t1, h5_J]
      rcases rmCmpLt_spec regS0 regLoopJ regS1 regS3 regS4 (by decide) (by decide) (by decide) (by decide)
          V inp t2 hi2.reg₁_le h1V with ⟨t3, ht3_fl, ht3_fr, hcmp3⟩
      have ht3_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
          k = regLoopNode ∨ k = regLoopW ∨ k = regEndU ∨ k = regS2 → t3 k = s5 k := by
        intro k hk
        have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regS1 ∨ q = regS3 ∨ q = regS4 → k ≠ q := by
          intro q hq heq; have hv := congrArg Fin.val heq
          rcases hk with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases hq with rfl | rfl | rfl | rfl <;> (try simp at hv) <;> omega
        rw [ht3_fr k (hne regS0 (Or.inl rfl)) (hne regS3 (Or.inr (Or.inr (Or.inl rfl))))
            (hne regS4 (Or.inr (Or.inr (Or.inr rfl))))]
        dsimp only [t2, t1]
        rw [regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl))), regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl)))]
      have ht3_S2 : t3 regS2 = w / 2 := by
        rw [ht3_keep regS2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))), hs5_S2]
      have hsubbr : ∃ qS t4,
          (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → t4 k = t3 k) ∧
          t4 regEndV = (if j < r then netV15 n + treeVertOff r (j + 1) + (node / 2) * (j + 2) + 1 + w / 2
                        else netV17 n + w / 2) ∧
          RMExec (rmIfZero regS0 (rmSetAdd regEndV regV17 regS2) rmB12DstParent rmSetAddEntry rmB12DstParentEntry)
            V inp rmIfZeroEntry t3 qS t4 [] (200 * n + 85) := by
        by_cases hjlt : j < r
        · have hfl2 : t3 regS0 ≠ 0 := by rw [ht3_fl, ht2_J, ht2_S1]; simp [hjlt]
          have hpt3 := hp5.of_preserved (fun k hk => ht3_keep k (Or.inl hk))
          rcases rmB12DstParent_spec n V j node w inp t3 hn hpt3 hcmp3.reg₁_le hV hj1 hjlt hnode hw
              (by rw [ht3_keep regLoopJ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h5_J])
              (by rw [ht3_keep regLoopNode (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
                      hs5_keep regLoopNode (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hN])
              ht3_S2
              (by rw [ht3_keep regLoopW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
                      hs5_keep regLoopW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), hW])
            with ⟨t4, ht4_keep, ht4_V, hpar⟩
          have hif2 := (rmIfZero_pos_spec regS0 (rmSetAdd regEndV regV17 regS2) rmSetAddEntry hfl2 hpar).weaken
            (V₂ := V) (T₂ := 200 * n + 85) (le_refl _) (by omega)
          refine ⟨_, t4, ht4_keep, by simp [hjlt, ht4_V, r], hif2⟩
        · have hfl2 : t3 regS0 = 0 := by rw [ht3_fl, ht2_J, ht2_S1]; simp [hjlt]
          have ht3_V17 : t3 regV17 = netV17 n := by
            rw [ht3_keep regV17 (Or.inl (by decide))]; exact hp5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have ha17 := rmSetAdd_spec regEndV regV17 regS2 (by decide) (by decide) (by decide)
            V inp t3 hcmp3.reg₁_le (by rw [ht3_V17, ht3_S2]; omega)
          have hif2 := (rmIfZero_zero_spec regS0 rmB12DstParent rmB12DstParentEntry hfl2 ha17).weaken
            (V₂ := V) (T₂ := 200 * n + 85) (le_refl _) (by rw [ht3_S2]; omega)
          refine ⟨_, _, ?_, by simp [hjlt, ht3_V17, ht3_S2], hif2⟩
          intro k hk
          have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regEndV → k ≠ q := by
            intro q hq heq; have hv := congrArg Fin.val heq
            rcases hk with hk | rfl | rfl | rfl <;> rcases hq with rfl | rfl <;> (try simp at hv) <;> omega
          rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndV (Or.inr rfl))]
      rcases hsubbr with ⟨qS, t4, ht4_keep, ht4_V, hif2⟩
      have hel := rmChain_spec_inl (by simp [rmCopy]) hc1
        (rmChain_spec_inl (by simp [rmInc]) hi2
          (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3 hif2))
      have hT_el : 2 + (1 + (1 + (2 * min (t2 regLoopJ) (t2 regS1) + 6 + (200 * n + 85)))) ≤ 220 * n + 100 := by
        rw [ht2_J, ht2_S1]; have : min j r ≤ r := min_le_right _ _; omega
      have hif := (rmIfZero_zero_spec regS0 rmB12DstThen (Sum.inl rmSetAddEntry) hfl hel).weaken
        (V₂ := V) (T₂ := 220 * n + 100) (by simp) hT_el
      simp only [List.nil_append] at hif
      refine ⟨_, t4, fun k hk => by
        have hk8 : k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
            k = regLoopNode ∨ k = regLoopW ∨ k = regEndU ∨ k = regS2 := by
          rcases hk with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        rw [ht4_keep k hk, ht3_keep k hk8],
        by simp [hcond, ht4_V], hif⟩
  rcases hbr with ⟨qB, s6, hs6_keep, hs6_V, hif6⟩
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc1
    (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd2
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha3
        (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp4
          (rmChain_spec_inl (by simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]) hif5 hif6))))
  have hT : 1 + 2 + (15 * s1 regS6 + 2 * s1 regS1 + 10 + (2 * s2 regLoopJ + 3 +
      (2 * min (s3 regS6) (s3 regS4) + 6 + (3 + (220 * n + 100))))) ≤ 300 * n + 150 := by
    have hs1S1 : s1 regS1 = 2 := by simp [s1]
    rw [hs1_S6, hs1S1, hs2_J, hs3_S6, hs3_S4]; have : min w (2 * j) ≤ 2 * j := min_le_right _ _
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 300 * n + 150) (by simp) hT
  simp only [List.nil_append] at hfin
  refine ⟨_, s6, fun k hk => by
    have hk8 : k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regLoopJ ∨
        k = regLoopNode ∨ k = regLoopW ∨ k = regEndU ∨ k = regS7 := by
      rcases hk with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    rw [hs6_keep k hk, hs5_keep k hk8], hs6_V, hfin⟩

/-- Full Block B12 emitter (`treeEdgeOff (treeLog n + 1) (treeLog n + 2)` edges). -/
abbrev RMB12BodyQ : Type := RMB12DecodeQ ⊕ (RMB12SrcQ ⊕ (RMB12DstQ ⊕ RMEmitEndPairQ))
abbrev RMEmitB12Q : Type := RMB12CountQ ⊕ RMForRangeQ RMB12BodyQ

def rmB12Body : RMProg EncR RMB12BodyQ :=
  rmChain rmB12Decode
    (rmChain rmB12Src (rmChain rmB12Dst rmEmitEndPair rmEmitEndPairEntry) (Sum.inl rmB12DstEntry))
    (Sum.inl rmIfZeroEntry)

def rmB12BodyEntry : RMB12BodyQ := Sum.inl rmB12DecodeEntry

def rmEmitB12 : RMProg EncR RMEmitB12Q :=
  rmChain rmB12Count (rmForRange regLoopI regLoopRem regLoopJ rmB12Body rmB12BodyEntry) rmForRangeEntry

def rmEmitB12Entry : RMEmitB12Q := Sum.inl rmB12CountEntry
def rmEmitB12Exit : RMEmitB12Q := Sum.inr rmForRangeExit

lemma rmEmitB12_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB12 V inp rmEmitB12Entry reg₀ rmEmitB12Exit reg₁
        ((List.range (treeEdgeOff (treeLog n + 1) (treeLog n + 2))).flatMap
          (fun e => emitEdgeBits (endsB12 n e)))
        (7000 * n ^ 3 + 110000 * n ^ 2 + 20000 * n + 100) := by
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have he12_le : treeEdgeOff (treeLog n + 1) (treeLog n + 2) ≤ 20 * n := by
    rw [treeEdgeOff_net]; omega
  rcases rmB12Count_spec n V inp reg₀ hn hp hreg₀ hV with ⟨r0, hr0_pr, hr0_J, hc0⟩
  rcases rmEdgeLoop_spec regLoopJ (by decide) rmB12Body rmB12BodyEntry
      V (300 * n ^ 2 + 5000 * n + 700) inp r0 (fun e => emitEdgeBits (endsB12 n e)) hc0.reg₁_le (by
        intro locE reg hloc hpr hreg hI
        have hp' := hp.of_preserved (hpr.trans hr0_pr)
        have hloc' : locE < treeEdgeOff (treeLog n + 1) (treeLog n + 2) := by omega
        set r := treeLog n + 1
        set t := decodeTreeEdge r locE
        rcases rmB12Decode_spec n V inp reg hn hp' hreg hV (by rw [hI]; exact hloc')
          with ⟨s1, h1pr, h1I, h1rem, ht1, htr, hnode, hw, h1J, h1N, h1S6, h1W, h1S7, hd1⟩
        rw [hI] at ht1 htr hnode hw h1J h1N h1S6 h1W h1S7
        rcases rmB12Src_spec n V t.1 t.2.1 t.2.2 inp s1 hn hd1.reg₁_le hV ht1 htr hnode hw h1S6 h1S7
          with ⟨q2, s2, h2keep, h2U, hs2⟩
        have hp2 := (hp'.of_preserved h1pr).of_preserved (fun k hk => h2keep k (Or.inl hk))
        rcases rmB12Dst_spec n V t.1 t.2.1 t.2.2 inp s2 hn hp2 hs2.reg₁_le hV ht1 htr hnode hw
            (by rw [h2keep regLoopJ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h1J])
            (by rw [h2keep regLoopNode (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), h1N])
            (by rw [h2keep regS6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))), h1S6])
            (by rw [h2keep regLoopW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), h1W])
            (by rw [h2keep regS7 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))), h1S7])
          with ⟨q3, s3, h3keep, h3V, hd3⟩
        have h3U : s3 regEndU = (endsB12 n locE).1 := by
          rw [h3keep regEndU (Or.inr (Or.inr (Or.inr rfl))), h2U]; rfl
        have h3V' : s3 regEndV = (endsB12 n locE).2 := by
          rw [h3V]; simp only [endsB12, bitIdx_eq_div2]; rfl
        have he := rmEmitEndPair_spec V inp s3 hd3.reg₁_le
        have hact_dec : rmB12Decode rmB12DecodeEntry ≠ none := by
          simp [rmB12Decode, rmB12DecodeEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
        have hact_src : rmB12Src rmIfZeroEntry ≠ none := by
          simp [rmB12Src, rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]
        have hact_dst : rmB12Dst rmB12DstEntry ≠ none := by
          simp [rmB12Dst, rmB12DstEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
        have hcomb := rmChain_spec_inl hact_dec hd1
          (rmChain_spec_inl hact_src hs2 (rmChain_spec_inl hact_dst hd3 he))
        have hU_le : s3 regEndU ≤ 500 * n + 20 := by
          have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
            simpa [r] using netV15_add_treeVertOff_le n
          have hvo_step := treeVertOff_step (r := r) ht1
          have hvo_mono := treeVertOff_mono r (show t.1 + 1 ≤ r + 1 by dsimp only [r, t] at htr ⊢; omega)
          have hnb : (t.2.1 + 1) * (t.1 + 1) ≤ (t.1 + 1) * 2 ^ (r - t.1) := by
            calc (t.2.1 + 1) * (t.1 + 1) ≤ 2 ^ (r - t.1) * (t.1 + 1) := Nat.mul_le_mul_right _ hnode
              _ = (t.1 + 1) * 2 ^ (r - t.1) := Nat.mul_comm _ _
          have hlin : (t.2.1 + 1) * (t.1 + 1) = t.2.1 * (t.1 + 1) + (t.1 + 1) := by ring
          rw [h3keep regEndU (Or.inr (Or.inr (Or.inr rfl))), h2U]
          dsimp only [r, t] at hv16_le hvo_step hvo_mono hnb hlin hw ⊢
          split_ifs <;> omega
        have hV_le : s3 regEndV ≤ 500 * n + 20 := by
          have hv16_le : netV15 n + treeVertOff r (r + 1) ≤ netVertCount n := by
            simpa [r] using netV15_add_treeVertOff_le n
          have hv18_le : netV17 n + (treeLog n + 2) ≤ netVertCount n := by
            simp only [netVertCount, netV18]; omega
          rw [h3V]
          split_ifs with hc hjlt
          · have hvo_step := treeVertOff_step (r := r) ht1
            have hvo_mono := treeVertOff_mono r (show t.1 + 1 ≤ r + 1 by dsimp only [r, t] at htr ⊢; omega)
            have hnb : (t.2.1 + 1) * (t.1 + 1) ≤ (t.1 + 1) * 2 ^ (r - t.1) := by
              calc (t.2.1 + 1) * (t.1 + 1) ≤ 2 ^ (r - t.1) * (t.1 + 1) := Nat.mul_le_mul_right _ hnode
                _ = (t.1 + 1) * 2 ^ (r - t.1) := Nat.mul_comm _ _
            have hlin : (t.2.1 + 1) * (t.1 + 1) = t.2.1 * (t.1 + 1) + (t.1 + 1) := by ring
            dsimp only [r, t] at hv16_le hvo_step hvo_mono hnb hlin hw ⊢
            omega
          · have hvo_step2 := treeVertOff_step (r := r) (show 1 ≤ t.1 + 1 by omega)
            have hvo_mono2 := treeVertOff_mono r (show t.1 + 2 ≤ r + 1 by dsimp only [r, t] at hjlt ⊢; omega)
            have hnd : t.2.1 / 2 < 2 ^ (r - (t.1 + 1)) := by
              have hexp : 2 ^ (r - t.1) = 2 * 2 ^ (r - (t.1 + 1)) := by
                have : r - t.1 = (r - (t.1 + 1)) + 1 := by dsimp only [r, t] at hjlt ⊢; omega
                rw [this, pow_succ']
              rw [hexp] at hnode; exact Nat.div_lt_of_lt_mul hnode
            have hnb : (t.2.1 / 2 + 1) * (t.1 + 2) ≤ (t.1 + 2) * 2 ^ (r - (t.1 + 1)) := by
              calc (t.2.1 / 2 + 1) * (t.1 + 2) ≤ 2 ^ (r - (t.1 + 1)) * (t.1 + 2) := Nat.mul_le_mul_right _ hnd
                _ = (t.1 + 2) * 2 ^ (r - (t.1 + 1)) := Nat.mul_comm _ _
            have hlin : (t.2.1 / 2 + 1) * (t.1 + 2) = (t.2.1 / 2) * (t.1 + 2) + (t.1 + 2) := by ring
            dsimp only [r, t] at hv16_le hvo_step2 hvo_mono2 hnb hlin hw ⊢
            have h12 : (decodeTreeEdge (treeLog n + 1) locE).1 + 1 + 1 =
                (decodeTreeEdge (treeLog n + 1) locE).1 + 2 := by omega
            rw [h12] at hvo_step2
            omega
          · dsimp only [r, t] at htr hw ⊢; omega
        have hT : 300 * n ^ 2 + 2500 * n + 400 +
            (100 * n + 50 + (300 * n + 150 + (2 * s3 regEndU + 2 * s3 regEndV + 6))) ≤
            300 * n ^ 2 + 5000 * n + 700 := by omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 300 * n ^ 2 + 5000 * n + 700) (by simp) hT
        simp only [List.nil_append, h3U, h3V', Prod.mk.eta] at hfin
        have h31pr : PreservedRegs s3 s1 := fun k hk => by rw [h3keep k (Or.inl hk), h2keep k (Or.inl hk)]
        exact ⟨_, regUpd s3 regS0 0,
          (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (h31pr.trans h1pr),
          by rw [regUpd_ne _ (by decide), h3keep regLoopI (Or.inr (Or.inl rfl)),
                 h2keep regLoopI (Or.inr (Or.inl rfl)), h1I, hI],
          by rw [regUpd_ne _ (by decide), h3keep regLoopRem (Or.inr (Or.inr (Or.inl rfl))),
                 h2keep regLoopRem (Or.inr (Or.inr (Or.inl rfl))), h1rem],
          hfin⟩)
    with ⟨reg₁, hpr₁, hloop⟩
  rw [hr0_J] at hloop
  have hcomb := rmChain_spec_inl
    (by simp [rmB12Count, rmB12CountEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]) hc0 hloop
  have hT : 200 * n + 50 + (treeEdgeOff (treeLog n + 1) (treeLog n + 2) *
      (300 * n ^ 2 + 5000 * n + 700 + 2) + 3) ≤
      7000 * n ^ 3 + 110000 * n ^ 2 + 20000 * n + 100 := by
    have hmul : treeEdgeOff (treeLog n + 1) (treeLog n + 2) * (300 * n ^ 2 + 5000 * n + 700 + 2) ≤
        20 * n * (300 * n ^ 2 + 5000 * n + 700 + 2) := Nat.mul_le_mul_right _ he12_le
    have hring : 20 * n * (300 * n ^ 2 + 5000 * n + 700 + 2) =
        6000 * n ^ 3 + 100000 * n ^ 2 + 14040 * n := by ring
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 7000 * n ^ 3 + 110000 * n ^ 2 + 20000 * n + 100) (by simp) hT
  simp only [List.nil_append] at hfin
  exact ⟨reg₁, hpr₁.trans hr0_pr, hfin⟩

/-! ### Edge Block Emitter B13 (`treeLog n + 3` Comparator-Chain Edges) -/

abbrev RMB13UNzQ : Type := Bool ⊕ (Bool ⊕ RMSetAddQ)
abbrev RMB13UQ : Type := Option Bool ⊕ (Bool ⊕ (Bool ⊕ RMB13UNzQ))
abbrev RMB13VQ : Type := Bool ⊕ (Fin 3 ⊕ (Fin 8 ⊕ (Option Bool ⊕ (Bool ⊕ (Bool ⊕ RMSetAddQ)))))
abbrev RMB13BodyQ : Type := RMB13UQ ⊕ (RMB13VQ ⊕ RMEmitEndPairQ)
abbrev RMEmitB13Q : Type := (Bool ⊕ Fin 4) ⊕ RMForRangeQ RMB13BodyQ

def rmB13UNz : RMProg EncR RMB13UNzQ :=
  rmChain (rmCopy regS1 regLoopI)
    (rmChain (rmDec1 regS1) (rmSetAdd regEndU regV17 regS1) rmSetAddEntry)
    (Sum.inl false)

def rmB13U : RMProg EncR RMB13UQ :=
  rmIfZero regLoopI (rmCopy regEndU regV16) rmB13UNz false (Sum.inl false)

def rmB13V : RMProg EncR RMB13VQ :=
  rmChain (rmCopy regS1 regTreeLog)
    (rmChain (rmAddConst regS1 2)
      (rmChain (rmCmpLt regS0 regLoopI regS1 regS2 regS3)
        (rmIfZero regS0 (rmCopy regEndV regV18) (rmSetAdd regEndV regV17 regLoopI) false rmSetAddEntry)
        rmIfZeroEntry)
      (Sum.inl 0))
    (Sum.inl ⟨0, by omega⟩)

def rmB13VEntry : RMB13VQ := Sum.inl false

def rmB13Body : RMProg EncR RMB13BodyQ :=
  rmChain rmB13U (rmChain rmB13V rmEmitEndPair rmEmitEndPairEntry) (Sum.inl rmB13VEntry)

def rmB13BodyEntry : RMB13BodyQ := Sum.inl rmIfZeroEntry

def rmEmitB13 : RMProg EncR RMEmitB13Q :=
  rmChain (rmChain (rmCopy regLoopJ regTreeLog) (rmAddConst regLoopJ 3) ⟨0, by omega⟩)
    (rmForRange regLoopI regLoopRem regLoopJ rmB13Body rmB13BodyEntry)
    rmForRangeEntry

def rmEmitB13Entry : RMEmitB13Q := Sum.inl (Sum.inl false)
def rmEmitB13Exit : RMEmitB13Q := Sum.inr rmForRangeExit

lemma rmEmitB13_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitB13 V inp rmEmitB13Entry reg₀ rmEmitB13Exit reg₁
        ((List.range (treeLog n + 3)).flatMap (fun e => emitEdgeBits (endsB13 n e)))
        (2500 * n ^ 2 + 8000 * n + 1000) := by
  have h1V : 1 ≤ V := by omega
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hvc := netVertCount_le hn
  have hv16_le : netV16 n ≤ netVertCount n := by simp only [netVertCount, netV18, netV17]; omega
  have hv18_le : netV17 n + (treeLog n + 2) ≤ netVertCount n := by simp only [netVertCount, netV18]; omega
  have hv18_def : netV18 n ≤ netVertCount n := by simp only [netVertCount]; omega
  have hTL : reg₀ regTreeLog = treeLog n := hp.2.2.2.2.2.2.2.2.2.2.1
  have hc0 := rmCopy_spec regLoopJ regTreeLog V inp reg₀ hreg₀
  set r0a := regUpd reg₀ regLoopJ (reg₀ regTreeLog)
  have ha0 := rmAddConst_spec regLoopJ 3 V inp r0a hc0.reg₁_le (by simp [r0a, hTL]; omega)
  set r0 := regUpd r0a regLoopJ (r0a regLoopJ + 3)
  have hpre0 := rmChain_spec_inl (by simp [rmCopy]) hc0 ha0
  have hr0_pr : PreservedRegs r0 reg₀ :=
    (PreservedRegs.upd_ge _ regLoopJ _ (by decide)).trans (PreservedRegs.upd_ge _ regLoopJ _ (by decide))
  have hr0_cnt : r0 regLoopJ = treeLog n + 3 := by simp [r0, r0a, hTL]
  rcases rmEdgeLoop_spec regLoopJ (by decide) rmB13Body rmB13BodyEntry
      V (2200 * n + 200) inp r0 (fun e => emitEdgeBits (endsB13 n e)) ha0.reg₁_le (by
        intro b reg hb hpr hreg hI
        have hp' := hp.of_preserved (hpr.trans hr0_pr)
        have hTL' : reg regTreeLog = treeLog n := hp'.2.2.2.2.2.2.2.2.2.2.1
        have hV16 : reg regV16 = netV16 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV17 : reg regV17 = netV17 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hV18 : reg regV18 = netV18 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hb' : b < treeLog n + 3 := by omega
        -- Compute U
        have hU_exec : ∃ qU s1,
            (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem → s1 k = reg k) ∧
            s1 regEndU = (if b = 0 then netV16 n else netV17 n + (b - 1)) ∧
            RMExec rmB13U V inp rmIfZeroEntry reg qU s1 [] (5 * n + 20) := by
          by_cases hb0 : b = 0
          · have hcp := rmCopy_spec regEndU regV16 V inp reg hreg
            have hif := (rmIfZero_zero_spec regLoopI rmB13UNz (Sum.inl false) (by rw [hI, hb0]) hcp).weaken
              (V₂ := V) (T₂ := 5 * n + 20) (le_refl _) (by omega)
            refine ⟨_, _, ?_, by simp [hb0, hV16], hif⟩
            intro k hk
            have hne : k ≠ regEndU := fun heq => by
              have hv := congrArg Fin.val heq
              rcases hk with hk | rfl | rfl <;> (try simp at hv); omega
            exact regUpd_ne reg hne _
          · have hc1 := rmCopy_spec regS1 regLoopI V inp reg hreg
            set t1 := regUpd reg regS1 (reg regLoopI)
            have hd2 := rmDec1_spec regS1 V inp t1 hc1.reg₁_le
            set t2 := regUpd t1 regS1 (t1 regS1 - 1)
            have ht2_S1 : t2 regS1 = b - 1 := by simp [t2, t1, hI]
            have ht2_V17 : t2 regV17 = netV17 n := by simp [t2, t1, hV17]
            have ha3 := rmSetAdd_spec regEndU regV17 regS1 (by decide) (by decide) (by decide)
              V inp t2 hd2.reg₁_le (by rw [ht2_V17, ht2_S1]; omega)
            have hnz := rmChain_spec_inl (by simp [rmCopy]) hc1
              (rmChain_spec_inl (by simp [rmDec1]) hd2 ha3)
            have hif := (rmIfZero_pos_spec regLoopI (rmCopy regEndU regV16) false (by rw [hI]; exact hb0) hnz).weaken
              (V₂ := V) (T₂ := 5 * n + 20) (by simp) (by rw [ht2_S1]; omega)
            simp only [List.nil_append] at hif
            refine ⟨_, _, ?_, by simp [hb0, ht2_V17, ht2_S1], hif⟩
            intro k hk
            have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regS1 ∨ q = regEndU → k ≠ q := by
              intro q hq heq; have hv := congrArg Fin.val heq
              rcases hk with hk | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> (try simp at hv) <;> omega
            dsimp only [t2, t1]
            rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndU (Or.inr (Or.inr rfl))),
                regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl))), regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl)))]
        rcases hU_exec with ⟨qU, s1, h1keep, h1U, hu1⟩
        have h1_I : s1 regLoopI = b := by rw [h1keep regLoopI (Or.inr (Or.inl rfl)), hI]
        have h1_TL : s1 regTreeLog = treeLog n := by rw [h1keep regTreeLog (Or.inl (by decide)), hTL']
        have h1_V17 : s1 regV17 = netV17 n := by rw [h1keep regV17 (Or.inl (by decide)), hV17]
        have h1_V18 : s1 regV18 = netV18 n := by rw [h1keep regV18 (Or.inl (by decide)), hV18]
        -- Compute V
        have hc1 := rmCopy_spec regS1 regTreeLog V inp s1 hu1.reg₁_le
        set t1 := regUpd s1 regS1 (s1 regTreeLog)
        have ha2 := rmAddConst_spec regS1 2 V inp t1 hc1.reg₁_le (by simp [t1, h1_TL]; omega)
        set t2 := regUpd t1 regS1 (t1 regS1 + 2)
        have ht2_S1 : t2 regS1 = treeLog n + 2 := by simp [t2, t1, h1_TL]
        have ht2_I : t2 regLoopI = b := by simp [t2, t1, h1_I]
        rcases rmCmpLt_spec regS0 regLoopI regS1 regS2 regS3 (by decide) (by decide) (by decide) (by decide)
            V inp t2 ha2.reg₁_le h1V with ⟨t3, ht3_fl, ht3_fr, hcmp3⟩
        have ht3_keep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU →
            t3 k = s1 k := by
          intro k hk
          have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regS1 ∨ q = regS2 ∨ q = regS3 → k ≠ q := by
            intro q hq heq; have hv := congrArg Fin.val heq
            rcases hk with hk | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> (try simp at hv) <;> omega
          rw [ht3_fr k (hne regS0 (Or.inl rfl)) (hne regS2 (Or.inr (Or.inr (Or.inl rfl))))
              (hne regS3 (Or.inr (Or.inr (Or.inr rfl))))]
          dsimp only [t2, t1]
          rw [regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl))), regUpd_ne _ (hne regS1 (Or.inr (Or.inl rfl)))]
        have ht3_I : t3 regLoopI = b := by rw [ht3_keep regLoopI (Or.inr (Or.inl rfl)), h1_I]
        have ht3_V17 : t3 regV17 = netV17 n := by rw [ht3_keep regV17 (Or.inl (by decide)), h1_V17]
        have ht3_V18 : t3 regV18 = netV18 n := by rw [ht3_keep regV18 (Or.inl (by decide)), h1_V18]
        have hV_br : ∃ qV s2,
            (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU → s2 k = t3 k) ∧
            s2 regEndV = (if b < treeLog n + 2 then netV17 n + b else netV18 n) ∧
            RMExec (rmIfZero regS0 (rmCopy regEndV regV18) (rmSetAdd regEndV regV17 regLoopI) false rmSetAddEntry)
              V inp rmIfZeroEntry t3 qV s2 [] (5 * n + 20) := by
          by_cases hlt : b < treeLog n + 2
          · have hfl : t3 regS0 ≠ 0 := by rw [ht3_fl, ht2_I, ht2_S1]; simp [hlt]
            have ha := rmSetAdd_spec regEndV regV17 regLoopI (by decide) (by decide) (by decide)
              V inp t3 hcmp3.reg₁_le (by rw [ht3_V17, ht3_I]; omega)
            have hif := (rmIfZero_pos_spec regS0 (rmCopy regEndV regV18) false hfl ha).weaken
              (V₂ := V) (T₂ := 5 * n + 20) (le_refl _) (by rw [ht3_I]; omega)
            refine ⟨_, _, ?_, by simp [hlt, ht3_V17, ht3_I], hif⟩
            intro k hk
            have hne : ∀ q : Fin EncR, q = regS0 ∨ q = regEndV → k ≠ q := by
              intro q hq heq; have hv := congrArg Fin.val heq
              rcases hk with hk | rfl | rfl | rfl <;> rcases hq with rfl | rfl <;> (try simp at hv) <;> omega
            rw [regUpd_ne _ (hne regS0 (Or.inl rfl)), regUpd_ne _ (hne regEndV (Or.inr rfl))]
          · have hfl : t3 regS0 = 0 := by rw [ht3_fl, ht2_I, ht2_S1]; simp [hlt]
            have hcp := rmCopy_spec regEndV regV18 V inp t3 hcmp3.reg₁_le
            have hif := (rmIfZero_zero_spec regS0 (rmSetAdd regEndV regV17 regLoopI) rmSetAddEntry hfl hcp).weaken
              (V₂ := V) (T₂ := 5 * n + 20) (le_refl _) (by omega)
            refine ⟨_, _, ?_, by simp [hlt, ht3_V18], hif⟩
            intro k hk
            have hne : k ≠ regEndV := fun heq => by
              have hv := congrArg Fin.val heq
              rcases hk with hk | rfl | rfl | rfl <;> (try simp at hv); omega
            exact regUpd_ne t3 hne _
        rcases hV_br with ⟨qV, s2, hs2_keep, hs2_V, hifV⟩
        have hv_exec := rmChain_spec_inl (by simp [rmCopy]) hc1
          (rmChain_spec_inl (by simp [rmAddConst]) ha2
            (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3 hifV))
        have hs2_U : s2 regEndU = (if b = 0 then netV16 n else netV17 n + (b - 1)) := by
          rw [hs2_keep regEndU (Or.inr (Or.inr (Or.inr rfl))),
              ht3_keep regEndU (Or.inr (Or.inr (Or.inr rfl))), h1U]
        have he := rmEmitEndPair_spec V inp s2 (by simpa using hv_exec.reg₁_le)
        have hact_U : rmB13U rmIfZeroEntry ≠ none := by
          simp [rmB13U, rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]
        have hact_V : rmB13V rmB13VEntry ≠ none := by
          simp [rmB13V, rmB13VEntry, rmChain, rmSeq, rmCopy]
        have hcomb := rmChain_spec_inl hact_U hu1 (rmChain_spec_inl hact_V hv_exec he)
        have hU_le : s2 regEndU ≤ 500 * n + 20 := by rw [hs2_U]; split_ifs <;> omega
        have hV_le : s2 regEndV ≤ 500 * n + 20 := by rw [hs2_V]; split_ifs <;> omega
        have hT : 5 * n + 20 + (1 + (2 + (2 * min (t2 regLoopI) (t2 regS1) + 6 + (5 * n + 20))) +
            (2 * s2 regEndU + 2 * s2 regEndV + 6)) ≤ 2200 * n + 200 := by
          rw [ht2_I, ht2_S1]; have : min b (treeLog n + 2) ≤ treeLog n + 2 := min_le_right _ _
          omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2200 * n + 200) (by simp) hT
        simp only [List.nil_append, hs2_U, hs2_V] at hfin
        have h2reg : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem →
            regUpd s2 regS0 0 k = reg k := fun k hk => by
          have hk4 : k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem ∨ k = regEndU := by
            rcases hk with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))
          have hne : k ≠ regS0 := fun heq => by
            have hv := congrArg Fin.val heq
            rcases hk with hk | rfl | rfl <;> (try simp at hv); omega
          rw [regUpd_ne _ hne, hs2_keep k hk4, ht3_keep k hk4, h1keep k hk]
        exact ⟨_, regUpd s2 regS0 0, fun k hk => h2reg k (Or.inl hk),
          by rw [h2reg regLoopI (Or.inr (Or.inl rfl)), hI],
          h2reg regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hloop⟩
  rw [hr0_cnt] at hloop
  have hcomb := rmChain_spec_inl (by simp [rmChain, rmSeq, rmCopy]) hpre0 hloop
  have hT : 1 + 3 + ((treeLog n + 3) * (2200 * n + 200 + 2) + 3) ≤ 2500 * n ^ 2 + 8000 * n + 1000 := by
    have hmul : (treeLog n + 3) * (2200 * n + 200 + 2) ≤ (n + 3) * (2200 * n + 200 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : (n + 3) * (2200 * n + 200 + 2) = 2200 * n ^ 2 + 6802 * n + 606 := by ring
    omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 2500 * n ^ 2 + 8000 * n + 1000) (by simp) hT
  simp only [List.nil_append] at hfin
  exact ⟨reg₁, hpr₁.trans hr0_pr, hfin⟩

/-! ### Complete Edge-List Emitter (`rmEmitAllEdges`) -/

abbrev RMEmitG0Q : Type := (RMEmitB0Q ⊕ RMEmitB1Q) ⊕ (RMEmitB2Q ⊕ RMEmitB3Q)
abbrev RMEmitG1Q : Type := (RMEmitDivModPairQ ⊕ RMEmitDivModPairQ) ⊕ (RMEmitDivModPairQ ⊕ RMEmitDivModPairQ)
abbrev RMEmitG2Q : Type := (RMEmitDivModPairQ ⊕ RMEmitDivModPairQ) ⊕ (RMEmitB10Q ⊕ RMEmitB11Q)
abbrev RMEmitG3Q : Type := RMEmitB12Q ⊕ RMEmitB13Q
abbrev RMEmitAllEdgesQ : Type := RMEmitG0Q ⊕ ((RMEmitG1Q ⊕ RMEmitG2Q) ⊕ RMEmitG3Q)

def rmEmitG0 : RMProg EncR RMEmitG0Q :=
  rmChain (rmChain rmEmitB0 rmEmitB1 rmForRangeEntry)
    (rmChain rmEmitB2 rmEmitB3 rmForRangeEntry)
    (Sum.inl rmEmitB2Entry)

def rmEmitG1 : RMProg EncR RMEmitG1Q :=
  rmChain (rmChain rmEmitB4 rmEmitB5 rmForRangeEntry)
    (rmChain rmEmitB6 rmEmitB7 rmForRangeEntry)
    (Sum.inl rmForRangeEntry)

def rmEmitG2 : RMProg EncR RMEmitG2Q :=
  rmChain (rmChain rmEmitB8 rmEmitB9 rmForRangeEntry)
    (rmChain rmEmitB10 rmEmitB11 rmForRangeEntry)
    (Sum.inl rmForRangeEntry)

def rmEmitG3 : RMProg EncR RMEmitG3Q :=
  rmChain rmEmitB12 rmEmitB13 rmEmitB13Entry

/-- Full edge-list emitter for `buildQCSDNet`: emits all `netEdgeCount n` endpoint pairs
`(rawEnds n e).1, (rawEnds n e).2` in unary across Blocks B0–B13. -/
def rmEmitAllEdges : RMProg EncR RMEmitAllEdgesQ :=
  rmChain rmEmitG0
    (rmChain (rmChain rmEmitG1 rmEmitG2 (Sum.inl (Sum.inl rmForRangeEntry)))
      rmEmitG3 (Sum.inl rmEmitB12Entry))
    (Sum.inl (Sum.inl (Sum.inl (Sum.inl rmForRangeEntry))))

def rmEmitAllEdgesEntry : RMEmitAllEdgesQ := Sum.inl (Sum.inl (Sum.inl rmForRangeEntry))
def rmEmitAllEdgesExit : RMEmitAllEdgesQ := Sum.inr (Sum.inr (Sum.inr rmEmitB13Exit))

lemma rmForRange_active {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R) (body : RMProg R Q) (q₀ : Q) :
    rmForRange rIdx rRem rCount body q₀ rmForRangeEntry ≠ none := by
  simp [rmForRange, rmForRangeEntry, rmChain, rmSeq, rmZero]

/-- Main Section 3b theorem: given `ParamsLoaded n reg₀` and `500 * n + 20 ≤ V`,
`rmEmitAllEdges` emits the EXACT unary edge list
`(List.range (netEdgeCount n)).flatMap (fun e => QCSD_natToUnary (rawEnds n e).1 ++ QCSD_natToUnary (rawEnds n e).2)`
in `O(n^3)` RM steps (explicitly `≤ 2000000 * n ^ 3`) with register bound `Vmax = V`,
preserving `ParamsLoaded n` and all input-parser registers (`regCur..regOffPre`). -/
theorem rmEmitAllEdges_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      ParamsLoaded n reg₁ ∧
      (∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec rmEmitAllEdges V inp rmEmitAllEdgesEntry reg₀ rmEmitAllEdgesExit reg₁
        ((List.range (netEdgeCount n)).flatMap (fun e =>
          QCSD_natToUnary (rawEnds n e).1 ++ QCSD_natToUnary (rawEnds n e).2))
        (2000000 * n ^ 3) := by
  rcases rmEmitB0_spec n V inp reg₀ hn hp hreg₀ hV with ⟨r1, hpr1, e0⟩
  have hp1 := hp.of_preserved hpr1
  rcases rmEmitB1_spec n V inp r1 hn hp1 e0.reg₁_le hV with ⟨r2, hpr2, e1⟩
  have hp2 := hp1.of_preserved hpr2
  rcases rmEmitB2_spec n V inp r2 hn hp2 e1.reg₁_le hV with ⟨r3, hpr3, e2⟩
  have hp3 := hp2.of_preserved hpr3
  rcases rmEmitB3_spec n V inp r3 hn hp3 e2.reg₁_le hV with ⟨r4, hpr4, e3⟩
  have hp4 := hp3.of_preserved hpr4
  rcases rmEmitB4_spec n V inp r4 hn hp4 e3.reg₁_le hV with ⟨r5, hpr5, e4⟩
  have hp5 := hp4.of_preserved hpr5
  rcases rmEmitB5_spec n V inp r5 hn hp5 e4.reg₁_le hV with ⟨r6, hpr6, e5⟩
  have hp6 := hp5.of_preserved hpr6
  rcases rmEmitB6_spec n V inp r6 hn hp6 e5.reg₁_le hV with ⟨r7, hpr7, e6⟩
  have hp7 := hp6.of_preserved hpr7
  rcases rmEmitB7_spec n V inp r7 hn hp7 e6.reg₁_le hV with ⟨r8, hpr8, e7⟩
  have hp8 := hp7.of_preserved hpr8
  rcases rmEmitB8_spec n V inp r8 hn hp8 e7.reg₁_le hV with ⟨r9, hpr9, e8⟩
  have hp9 := hp8.of_preserved hpr9
  rcases rmEmitB9_spec n V inp r9 hn hp9 e8.reg₁_le hV with ⟨r10, hpr10, e9⟩
  have hp10 := hp9.of_preserved hpr10
  rcases rmEmitB10_spec n V inp r10 hn hp10 e9.reg₁_le hV with ⟨r11, hpr11, e10⟩
  have hp11 := hp10.of_preserved hpr11
  rcases rmEmitB11_spec n V inp r11 hn hp11 e10.reg₁_le hV with ⟨r12, hpr12, e11⟩
  have hp12 := hp11.of_preserved hpr12
  rcases rmEmitB12_spec n V inp r12 hn hp12 e11.reg₁_le hV with ⟨r13, hpr13, e12⟩
  have hp13 := hp12.of_preserved hpr13
  rcases rmEmitB13_spec n V inp r13 hn hp13 e12.reg₁_le hV with ⟨r14, hpr14, e13⟩
  have hact_b2 : rmEmitB2 rmEmitB2Entry ≠ none := by
    simp [rmEmitB2, rmEmitB2Entry, rmChain, rmSeq, rmSetAdd, rmSetAddEntry, rmCopy]
  have hact_b12 : rmEmitB12 rmEmitB12Entry ≠ none := by
    simp [rmEmitB12, rmEmitB12Entry, rmB12Count, rmB12CountEntry, rmChain, rmSeq,
      rmSetConst, rmSetConstEntry, rmZero]
  have eg0a := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e0 e1
  have eg0b := rmChain_spec_inl hact_b2 e2 e3
  have eg0 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg0a eg0b
  have eg1a := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e4 e5
  have eg1b := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e6 e7
  have eg1 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg1a eg1b
  have eg2a := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e8 e9
  have eg2b := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e10 e11
  have eg2 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg2a eg2b
  have eg3 := rmChain_spec_inl hact_b12 e12 e13
  have eg12 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg1 eg2
  have eg123 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg12 eg3
  have hall := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eg0 eg123
  have hT_le :
      ((40 * n ^ 2 + 30 * n + 10 + (5000 * n ^ 2 + 500 * n + 10)) +
       (10000 * n ^ 2 + 1000 * n + 20 + (2500 * n ^ 2 + 300 * n + 10))) +
      (((200000 * n ^ 2 + 12000 * n + 10 + (200000 * n ^ 2 + 12000 * n + 10)) +
        (200000 * n ^ 2 + 12000 * n + 10 + (200000 * n ^ 2 + 12000 * n + 10)) +
        ((200000 * n ^ 2 + 12000 * n + 10 + (200000 * n ^ 2 + 12000 * n + 10)) +
         (250000 * n ^ 2 + 15000 * n + 10 + (5000 * n ^ 2 + 500 * n + 10)))) +
       (7000 * n ^ 3 + 110000 * n ^ 2 + 20000 * n + 100 + (2500 * n ^ 2 + 8000 * n + 1000))) ≤
      2000000 * n ^ 3 := by
    have hn2 : n ^ 2 ≤ n ^ 3 := by
      have : n ^ 3 = n ^ 2 * n := by ring
      rw [this]; exact Nat.le_mul_of_pos_right _ hn
    have hn1 : n ≤ n ^ 3 := by
      have : n ≤ n ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ hn
      omega
    have h1n3 : 1 ≤ n ^ 3 := by omega
    omega
  have hfin := hall.weaken (V₂ := V) (T₂ := 2000000 * n ^ 3) (by simp) hT_le
  have hout :
      (((List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB0 n e)) ++
        (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB1 n e))) ++
       ((List.range (2 * treeM n)).flatMap (fun e => emitEdgeBits (endsB2 n e)) ++
        (List.range n).flatMap (fun e => emitEdgeBits (endsB3 n e)))) ++
      ((((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB4 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB5 n e))) ++
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB6 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB7 n e)))) ++
       (((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB8 n e)) ++
         (List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB9 n e))) ++
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun e => emitEdgeBits (endsB10 n e)) ++
         (List.range (2 * n)).flatMap (fun e => emitEdgeBits (endsB11 n e)))) ++
       ((List.range (treeEdgeOff (treeLog n + 1) (treeLog n + 2))).flatMap
          (fun e => emitEdgeBits (endsB12 n e)) ++
        (List.range (treeLog n + 3)).flatMap (fun e => emitEdgeBits (endsB13 n e)))) =
      (List.range (netEdgeCount n)).flatMap (fun e =>
        QCSD_natToUnary (rawEnds n e).1 ++ QCSD_natToUnary (rawEnds n e).2) := by
    rw [← flatMap_range_rawEnds_eq n]; rfl
  rw [hout] at hfin
  have hpr_all : PreservedRegs r14 reg₀ :=
    hpr14.trans (hpr13.trans (hpr12.trans (hpr11.trans (hpr10.trans (hpr9.trans
      (hpr8.trans (hpr7.trans (hpr6.trans (hpr5.trans (hpr4.trans (hpr3.trans (hpr2.trans hpr1))))))))))))
  exact ⟨r14, hp.of_preserved hpr_all, fun i _ hi2 => hpr_all i (by omega), hfin⟩

end Branch6Encoder
