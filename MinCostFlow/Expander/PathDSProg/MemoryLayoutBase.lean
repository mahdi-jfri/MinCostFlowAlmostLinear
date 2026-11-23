module

public import MinCostFlow.Expander.PathDSProg.MaskProjProg
public import MinCostFlow.Expander.PathDSProg.BoundsProg
public import MinCostFlow.Expander.DecomposePartBase
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.GraphHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Memory Layout, Footprint, Potential and Size Bounds

This file holds the first part of the material of `MemoryLayout.lean`, split off to keep files
small. `MemoryLayout.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Header Layout, Concrete State, Footprint, and Potential -/

/-- Size in words of the fixed metadata header at handle `b = hInit`. -/
abbrev hdrSize : ℕ := 18

abbrev hdrMode : ℕ := 0
abbrev hdrN : ℕ := 1
abbrev hdrM : ℕ := 2
abbrev hdrPhiNum : ℕ := 3
abbrev hdrPhiDen : ℕ := 4
abbrev hdrMCap : ℕ := 5
abbrev hdrGsAddr : ℕ := 6
abbrev hdrInVhat : ℕ := 7
abbrev hdrCsHandle : ℕ := 8
abbrev hdrDelCount : ℕ := 9
abbrev hdrCsDelCap : ℕ := 10
abbrev hdrOverBudget : ℕ := 11
abbrev hdrCsrAddr : ℕ := 12
abbrev hdrInBAddr : ℕ := 13
abbrev hdrOutRAddr : ℕ := 14
abbrev hdrEMaskAddr : ℕ := 15
abbrev hdrAllocEnd : ℕ := 16
abbrev hdrQVal : ℕ := 17

/-- Concrete internal Word-RAM representation state paired with `PathDSAbsState`. -/
inductive PathDSConcrete (τ_cs : Type) where
  | cs (s_cs : PrunedExpander) (x_cs : τ_cs) (csHandle csDelCap : ℕ) (overBudget : Bool)
      (g_sAddr inVhatAddr allocEnd : ℕ)
  | fb (g_sAddr inVhatAddr csrAddr inBAddr outRAddr eMaskAddr allocEnd : ℕ) (R_fb : Finset ℕ)

/-- Memory footprint `[b, allocEnd)` unioned with `[CS21]`'s internal footprint when active. -/
def pathDSFoot (R_cs : DSRep PrunedExpander) (b : ℕ) : PathDSConcrete R_cs.τ → ℕ → Prop
  | .cs _ x_cs csHandle _ _ _ _ allocEnd, a => (b ≤ a ∧ a < allocEnd) ∨ R_cs.foot csHandle x_cs a
  | .fb _ _ _ _ _ _ allocEnd _, a => b ≤ a ∧ a < allocEnd

/-- Potential function: `2 * R_cs.phi + 75 * (G_s.n - s_cs.S.card) + 55 * G_s.n + 100` in live
`[CS21]` mode, and `0` in fallback mode or after `overBudget`. -/
def pathDSPhi (R_cs : DSRep PrunedExpander) : PathDSConcrete R_cs.τ → (ℕ → ℕ) → ℕ
  | .cs s_cs x_cs csHandle _ false _ _ _, mem =>
      2 * R_cs.phi csHandle x_cs mem + 75 * (s_cs.G.n - s_cs.S.card) + 55 * s_cs.G.n + 100
  | .cs _ _ _ _ true _ _ _, _ => 0
  | .fb _ _ _ _ _ _ _ _, _ => 0

/-- Representation invariant linking `PathDSAbsState`, `PathDSConcrete`, and Word-RAM memory
(with mathematical witness `K : ℝ` for `PrunedExpander.Good`). -/
def pathDSRepProp (Kγ c K_int cw_cs : ℕ) (K : ℝ) (R_cs : DSRep PrunedExpander)
    (b : ℕ) (s : PathDSAbsState) (x : PathDSConcrete R_cs.τ) (mem : ℕ → ℕ) : Prop :=
  let G_s := subdivGraph s.G
  let n_s := G_s.n
  let m_s := G_s.m
  let d := (s.phiDen + s.phiNum - 1) / s.phiNum
  let C_cap := 40 * d + 1
  s.Valid (pathDSParams Kγ c K_int cw_cs) ∧
  mem (b + hdrN) = s.G.n ∧
  mem (b + hdrM) = s.G.m ∧
  mem (b + hdrPhiNum) = s.phiNum ∧
  mem (b + hdrPhiDen) = s.phiDen ∧
  mem (b + hdrMCap) = s.M ∧
  mem (b + hdrDelCount) = s.deleted.card ∧
  mem (b + hdrQVal) = qOf s.M ∧
  (match x with
   | .cs s_cs x_cs csHandle csDelCap overBudget g_sAddr inVhatAddr allocEnd =>
      10 * Cited.csPhi Kγ c (3 * s.G.m) ≤ s.φ_in ∧
      g_sAddr = b + hdrSize ∧
      inVhatAddr = g_sAddr + 2 + 6 * s.G.m ∧
      allocEnd = inVhatAddr + s.G.n ∧
      csHandle = allocEnd ∧
      csDelCap = (3 * s.G.m) / (10 * c * Cited.csGamma Kγ (3 * s.G.m)) ∧
      mem (b + hdrMode) = 0 ∧
      mem (b + hdrGsAddr) = g_sAddr ∧
      mem (b + hdrInVhat) = inVhatAddr ∧
      mem (b + hdrCsHandle) = csHandle ∧
      mem (b + hdrCsDelCap) = csDelCap ∧
      mem (b + hdrOverBudget) = (if overBudget then 1 else 0) ∧
      mem (b + hdrAllocEnd) = allocEnd ∧
      GraphAt mem g_sAddr G_s ∧
      (∀ v < s.G.n, mem (inVhatAddr + v) = if v ∈ s.Vhat then 1 else 0) ∧
      s_cs.G = G_s ∧
      s_cs.q = qOf s.M ∧
      (∀ a, R_cs.foot csHandle x_cs a → allocEnd ≤ a) ∧
      R_cs.rep csHandle s_cs x_cs mem ∧
      (if overBudget = false then
        s.deleted.card ≤ csDelCap ∧
        s_cs.deleted.toFinset = s.deleted.image (fun j => 3 * j + 1) ∧
        s_cs.deleted.Nodup ∧
        s_cs.deleted.length = s.deleted.card ∧
        PrunedExpander.Good K (Cited.csPhi Kγ c G_s.m) s_cs ∧
        s.Vhat = projSet s.G.n s_cs.S
      else
        csDelCap + 1 ≤ s.deleted.card ∧
        s.Vhat = s.G.verts)
   | .fb g_sAddr inVhatAddr csrAddr inBAddr outRAddr eMaskAddr allocEnd R_fb =>
      s.φ_in < 10 * Cited.csPhi Kγ c (3 * s.G.m) ∧
      3 * s.G.m < zStarImpl d ∧
      g_sAddr = b + hdrSize ∧
      inVhatAddr = g_sAddr + 2 + 6 * s.G.m ∧
      csrAddr = inVhatAddr + s.G.n ∧
      inBAddr = csrAddr + (2 * n_s + 1 + 4 * m_s) ∧
      outRAddr = inBAddr + n_s ∧
      eMaskAddr = outRAddr + n_s ∧
      allocEnd = eMaskAddr + m_s ∧
      mem (b + hdrMode) = 1 ∧
      mem (b + hdrGsAddr) = g_sAddr ∧
      mem (b + hdrInVhat) = inVhatAddr ∧
      mem (b + hdrCsrAddr) = csrAddr ∧
      mem (b + hdrInBAddr) = inBAddr ∧
      mem (b + hdrOutRAddr) = outRAddr ∧
      mem (b + hdrEMaskAddr) = eMaskAddr ∧
      mem (b + hdrAllocEnd) = allocEnd ∧
      GraphAt mem g_sAddr G_s ∧
      HasCsrAt mem csrAddr G_s ∧
      (∀ v < s.G.n, mem (inVhatAddr + v) = if v ∈ s.Vhat then 1 else 0) ∧
      (∀ v < n_s, mem (outRAddr + v) = if v ∈ R_fb then 1 else 0) ∧
      (∀ j < m_s, mem (eMaskAddr + j) = if ∃ e ∈ s.deleted, j = 3 * e + 1 then 0 else 1) ∧
      R_fb ⊆ G_s.verts ∧
      (∀ e ∈ s.deleted, s.G.n + 2 * e ∉ R_fb ∧ s.G.n + 2 * e + 1 ∉ R_fb) ∧
      G_s.IsConductanceExpanderOn R_fb (s.φ_in / 30) ∧
      (∀ z ∈ R_fb, 1 ≤ G_s.degIn R_fb z) ∧
      s.Vhat = s.G.verts \ R_fb ∧
      G_s.volIn G_s.verts (G_s.verts \ R_fb) + 2 * C_cap * G_s.cutIn G_s.verts R_fb ≤
        s.deleted.card * (4 * C_cap + 4))

def pathDSRep (Kγ c K_int cw_cs : ℕ) (K : ℝ) (R_cs : DSRep PrunedExpander) :
    DSRep PathDSAbsState where
  τ := PathDSConcrete R_cs.τ
  rep := pathDSRepProp Kγ c K_int cw_cs K R_cs
  phi _ x mem := pathDSPhi R_cs x mem
  foot b x a := pathDSFoot R_cs b x a

lemma graphAt_congr {mem mem' : ℕ → ℕ} {a : ℕ} {G : Cited.Graph}
    (h : ∀ addr, a ≤ addr → addr < a + G.encode.length → mem addr = mem' addr)
    (hG : GraphAt mem a G) : GraphAt mem' a G := by
  have h0 : mem' a = G.n := by rw [← h a (by omega) (by rw [graph_encode_length]; omega)]; exact graphAt_n hG
  have h1 : mem' (a + 1) = G.m := by rw [← h (a + 1) (by omega) (by rw [graph_encode_length]; omega)]; exact graphAt_m hG
  refine graphAt_of_cells h0 h1 fun j hj => ?_
  have hj1 : a + 2 + 2 * j < a + G.encode.length := by rw [graph_encode_length]; omega
  have hj2 : a + 3 + 2 * j < a + G.encode.length := by rw [graph_encode_length]; omega
  exact ⟨by rw [← h _ (by omega) hj1]; exact graphAt_edge_fst hG hj,
    by rw [← h _ (by omega) hj2]; exact graphAt_edge_snd hG hj⟩

lemma hasCsrAt_congr {mem mem' : ℕ → ℕ} {a : ℕ} {G : Cited.Graph}
    (h : ∀ addr, a ≤ addr → addr < a + 2 * G.n + 1 + 4 * G.m → mem addr = mem' addr)
    (hC : HasCsrAt mem a G) : HasCsrAt mem' a G := by
  refine ⟨fun u hu => ?_, fun u hu j hj => ?_⟩
  · rw [← h (a + u) (by omega) (by omega)]; exact hC.1 u hu
  · have hsum : csrOff G u + j < 2 * G.m := by
      have h1 : csrOff G u + (csrIncAux u 0 G.edges).length = csrOff G (u + 1) := (csrOff_succ G u).symm
      have h2 := csrOff_le_two_mul_m G (u + 1)
      omega
    have hq := hC.2 u hu j hj
    refine ⟨?_, ?_⟩
    · rw [← h _ (by omega) (by omega)]; exact hq.1
    · rw [← h _ (by omega) (by omega)]; exact hq.2

lemma pathDSRep_local (Kγ c K_int cw_cs : ℕ) (K : ℝ) {R_cs : DSRep PrunedExpander}
    (hL : R_cs.Local) : (pathDSRep Kγ c K_int cw_cs K R_cs).Local := by
  intro b s x mem mem' hmem
  cases x with
  | cs s_cs x_cs csHandle csDelCap overBudget g_sAddr inVhatAddr allocEnd =>
    have hsub : ∀ addr, b ≤ addr → addr < allocEnd → mem addr = mem' addr :=
      fun addr h1 h2 => hmem addr (Or.inl ⟨h1, h2⟩)
    have hsub_cs : ∀ addr, R_cs.foot csHandle x_cs addr → mem addr = mem' addr :=
      fun addr ha => hmem addr (Or.inr ha)
    have hcs := hL csHandle s_cs x_cs mem mem' hsub_cs
    refine ⟨fun hr => ?_, ?_⟩
    · rcases hr with ⟨hval, h1, h2, h3, h4, h5, h6, h7, hcsφ, rfl, rfl, rfl, rfl, rfl,
        hm0, hm6, hm7, hm8, hm10, hm11, hm16, hGs, hinV, hcsG, hcsq, hfoot, hcsrep, hbr⟩
      have heq_hdr : ∀ k < hdrSize, mem (b + k) = mem' (b + k) :=
        fun k hk => hsub (b + k) (by omega) (by omega)
      refine ⟨hval,
        by rw [← heq_hdr _ (by decide), h1], by rw [← heq_hdr _ (by decide), h2],
        by rw [← heq_hdr _ (by decide), h3], by rw [← heq_hdr _ (by decide), h4],
        by rw [← heq_hdr _ (by decide), h5], by rw [← heq_hdr _ (by decide), h6],
        by rw [← heq_hdr _ (by decide), h7], hcsφ, rfl, rfl, rfl, rfl, rfl,
        by rw [← heq_hdr _ (by decide), hm0], by rw [← heq_hdr _ (by decide), hm6],
        by rw [← heq_hdr _ (by decide), hm7], by rw [← heq_hdr _ (by decide), hm8],
        by rw [← heq_hdr _ (by decide), hm10], by rw [← heq_hdr _ (by decide), hm11],
        by rw [← heq_hdr _ (by decide), hm16],
        graphAt_congr (fun a ha1 ha2 => hsub a (by omega) (by
          rw [graph_encode_length, subdivGraph_m] at ha2; omega)) hGs,
        fun v hv => by rw [← hsub (b + hdrSize + 2 + 6 * s.G.m + v) (by omega) (by omega)]; exact hinV v hv,
        hcsG, hcsq, hfoot, hcs.1 hcsrep, hbr⟩
    · cases overBudget
      · dsimp only [pathDSRep, pathDSPhi]; rw [hcs.2]
      · rfl
  | fb g_sAddr inVhatAddr csrAddr inBAddr outRAddr eMaskAddr allocEnd R_fb =>
    have hsub : ∀ addr, b ≤ addr → addr < allocEnd → mem addr = mem' addr :=
      fun addr h1 h2 => hmem addr ⟨h1, h2⟩
    refine ⟨fun hr => ?_, rfl⟩
    rcases hr with ⟨hval, h1, h2, h3, h4, h5, h6, h7, hlt1, hlt2, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hm0, hm6, hm7, hm12, hm13, hm14, hm15, hm16, hGs, hCsr, hinV, houtR, heM,
      hRsub, hmidR, hexpR, hdegR, hVh, hpot⟩
    have heq_hdr : ∀ k < hdrSize, mem (b + k) = mem' (b + k) :=
      fun k hk => hsub (b + k) (by omega) (by omega)
    refine ⟨hval,
      by rw [← heq_hdr _ (by decide), h1], by rw [← heq_hdr _ (by decide), h2],
      by rw [← heq_hdr _ (by decide), h3], by rw [← heq_hdr _ (by decide), h4],
      by rw [← heq_hdr _ (by decide), h5], by rw [← heq_hdr _ (by decide), h6],
      by rw [← heq_hdr _ (by decide), h7], hlt1, hlt2, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by rw [← heq_hdr _ (by decide), hm0], by rw [← heq_hdr _ (by decide), hm6],
      by rw [← heq_hdr _ (by decide), hm7], by rw [← heq_hdr _ (by decide), hm12],
      by rw [← heq_hdr _ (by decide), hm13], by rw [← heq_hdr _ (by decide), hm14],
      by rw [← heq_hdr _ (by decide), hm15], by rw [← heq_hdr _ (by decide), hm16],
      graphAt_congr (fun a ha1 ha2 => hsub a (by omega) (by
        rw [graph_encode_length, subdivGraph_m] at ha2; omega)) hGs,
      hasCsrAt_congr (fun a ha1 ha2 => hsub a (by omega) (by omega)) hCsr,
      fun v hv => by rw [← hsub _ (by omega) (by omega)]; exact hinV v hv,
      fun v hv => by rw [← hsub _ (by omega) (by omega)]; exact houtR v hv,
      fun j hj => by rw [← hsub _ (by omega) (by omega)]; exact heM j hj,
      hRsub, hmidR, hexpR, hdegR, hVh, hpot⟩

/-! ## 2. Word-Size, Heap-Space, and Cost Bounds -/

private lemma ceil_div_le_den {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b + a - 1) / a ≤ b := by
  apply Nat.div_le_of_le_mul
  have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a (by omega)
  have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  by_cases ha1 : a = 1
  · subst ha1; omega
  · have h2b : 2 * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
    omega

lemma edge_valid_lt {G : Cited.Graph} (hV : G.IsValid) {j : ℕ} (hj : j < G.m) :
    (G.edges.getD j (0, 0)).1 < G.n ∧ (G.edges.getD j (0, 0)).2 < G.n := by
  have hj' : j < G.edges.length := hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using hV _ (List.getElem_mem hj')

lemma cw_world_bounds {Kγ c K_int cw_cs w : ℕ}
    {phiNum phiDen n m M : ℕ} (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hKγ : 1 ≤ Kγ) (_hc : 1 ≤ c) (hK1 : 1 ≤ K_int) (_hKγ_le : Kγ ≤ K_int)
    (hw : (pathDSParams Kγ c K_int cw_cs).cw *
      (Nat.log 2 (n + m + phiDen + M +
        Nat.ceil ((pathDSParams Kγ c K_int cw_cs).γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M) + 2) + 1) ≤ w) :
    let d := (phiDen + phiNum - 1) / phiNum
    let X := n + m + phiDen + M + gExpImpl Kγ c K_int d M + 2
    1 ≤ d ∧ d ≤ phiDen ∧ X ^ 24 < 2 ^ w ∧
    16 ≤ X ^ 4 ∧
    cw_cs * (Nat.log 2 ((n + 2 * m) + 3 * m + 2) + 1) ≤ w ∧
    Kγ < 2 ^ w ∧ c < 2 ^ w ∧ qOf M < 2 ^ w ∧
    10 * c * Cited.csGamma Kγ (3 * m) < 2 ^ w := by
  intro d X
  have hd_ge1 : 1 ≤ d := Nat.div_pos (by omega) hpn
  have hd_le : d ≤ phiDen := ceil_div_le_den hpn hpd
  have hceil_d : Nat.ceil (1 / ((phiNum : ℝ) / (phiDen : ℝ))) = d :=
    nat_ceil_div_eq hpn hpd
  have hγ_eq : Nat.ceil ((pathDSParams Kγ c K_int cw_cs).γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M) =
      gExpImpl Kγ c K_int d M := by
    unfold PathDSParams.γ_ExpPath
    dsimp only [pathDSParams]
    rw [hceil_d]
    exact Nat.ceil_natCast _
  rw [hγ_eq] at hw
  have hcw24 : 24 * (Nat.log 2 X + 1) ≤ w :=
    le_trans (Nat.mul_le_mul_right _ (le_max_left 24 (4 * cw_cs + 8))) hw
  have hcw_cs : (4 * cw_cs + 8) * (Nat.log 2 X + 1) ≤ w :=
    le_trans (Nat.mul_le_mul_right _ (le_max_right 24 (4 * cw_cs + 8))) hw
  have hlogX : X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by decide) X
  have hX24 : X ^ 24 < 2 ^ w := by
    calc X ^ 24 < (2 ^ (Nat.log 2 X + 1)) ^ 24 := Nat.pow_lt_pow_left hlogX (by decide)
      _ = 2 ^ (24 * (Nat.log 2 X + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hcw24
  have hphi_ge2 : 2 ≤ phiOutDenImpl Kγ c d M := by unfold phiOutDenImpl; omega
  have hg_phi : phiOutDenImpl Kγ c d M ≤ gExpImpl Kγ c K_int d M :=
    phiOutDenImpl_le_gExpImpl Kγ c K_int _ _
  have hg_ge : c * Cited.csGamma Kγ (3 * M) ≤ gExpImpl Kγ c K_int d M :=
    le_trans (by unfold phiOutDenImpl; omega) hg_phi
  have hg1 : 2 ^ csGammaExp Kγ (4 * M) ≤ csExpFactor Kγ K_int M := by
    unfold csExpFactor
    have hq2 : 2 ≤ qOf M := qOf_ge_two M
    have hexp : csGammaExp Kγ (4 * M) ≤ csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M := by
      have : 1 ≤ K_int * qOf M := Nat.mul_pos hK1 (by omega)
      nlinarith
    exact le_trans (Nat.pow_le_pow_right (by decide) hexp) (Nat.le_add_right _ _)
  have hcs_lt : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int d M :=
      csExpFactor_le_gExpImpl Kγ c K_int _ _
  have hg_ge8 : 8 ≤ gExpImpl Kγ c K_int d M := by
    have hlog4 : 2 ≤ Nat.log 2 (4 * M) :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
    have hsq3 : 2 ≤ ((Nat.log 2 (4 * M) + 1) ^ 3).sqrt.sqrt := by
      have hpow3 : 27 ≤ (Nat.log 2 (4 * M) + 1) ^ 3 :=
        le_trans (by decide : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_left (by omega) 3)
      have hsq1 : 5 ≤ ((Nat.log 2 (4 * M) + 1) ^ 3).sqrt := Nat.le_sqrt.mpr (by omega)
      exact Nat.le_sqrt.mpr (by omega)
    have hce3 : 3 ≤ csGammaExp Kγ (4 * M) := by
      unfold csGammaExp
      have h13 : 1 * 3 ≤ Kγ * (((Nat.log 2 (4 * M) + 1) ^ 3).sqrt.sqrt + 1) :=
        Nat.mul_le_mul hKγ (by omega)
      omega
    have h2_3 : 8 ≤ 2 ^ csGammaExp Kγ (4 * M) :=
      le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) hce3)
    exact le_trans h2_3 (le_trans hg1 hcs_lt)
  have hX8 : 8 ≤ X := by dsimp [X]; omega
  have hX4 : 16 ≤ X ^ 4 := by
    have : 8 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hX8 4
    omega
  have hX_lt : X < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow (by decide) X) hX24
  have hc_lt : c < 2 ^ w := by
    have hcs1 : 1 ≤ Cited.csGamma Kγ (3 * M) := by rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ _ (by decide)
    have h1 : c ≤ c * Cited.csGamma Kγ (3 * M) := Nat.le_mul_of_pos_right c hcs1
    have h2 : c < X := by dsimp [X]; omega
    exact lt_trans h2 hX_lt
  have hKγ_lt : Kγ < 2 ^ w := by
    have hKγ_exp : Kγ ≤ csGammaExp Kγ (4 * M) := by
      unfold csGammaExp
      exact Nat.le_mul_of_pos_right Kγ (Nat.succ_pos _)
    have hpow : Kγ < 2 ^ Kγ := Nat.lt_two_pow_self
    have : Kγ < X := by
      calc Kγ < 2 ^ Kγ := hpow
        _ ≤ 2 ^ csGammaExp Kγ (4 * M) := Nat.pow_le_pow_right (by decide) hKγ_exp
        _ ≤ csExpFactor Kγ K_int M := hg1
        _ ≤ gExpImpl Kγ c K_int d M := hcs_lt
        _ < X := by dsimp [X]; omega
    exact lt_trans this hX_lt
  have hq_lt : qOf M < 2 ^ w := by
    have hq_pow : qOf M < X := by
      have : qOf M ≤ M + 3 := by
        rw [qOf_eq_qRoot_add_two]
        have hq8 := qRoot_pow_eight_le M
        have hq_le : qRoot M ≤ (qRoot M) ^ 8 := Nat.le_self_pow (by decide) _
        have hlog : Nat.log 2 (M + 2) < M + 2 := Nat.log_lt_self 2 (by omega)
        omega
      dsimp [X]; omega
    exact lt_trans hq_pow hX_lt
  have h10c_lt : 10 * c * Cited.csGamma Kγ (3 * m) < 2 ^ w := by
    have hm' : Cited.csGamma Kγ (3 * m) ≤ Cited.csGamma Kγ (3 * M) := csGamma_mono (by omega)
    have hprod : 10 * c * Cited.csGamma Kγ (3 * m) ≤ 10 * X := by
      have hcm : c * Cited.csGamma Kγ (3 * m) ≤ c * Cited.csGamma Kγ (3 * M) := Nat.mul_le_mul_left c hm'
      have hcx : c * Cited.csGamma Kγ (3 * m) ≤ X := by
        calc c * Cited.csGamma Kγ (3 * m) ≤ c * Cited.csGamma Kγ (3 * M) := hcm
          _ ≤ gExpImpl Kγ c K_int d M := hg_ge
          _ ≤ X := by dsimp [X]; omega
      calc 10 * c * Cited.csGamma Kγ (3 * m) = 10 * (c * Cited.csGamma Kγ (3 * m)) := mul_assoc _ _ _
        _ ≤ 10 * X := Nat.mul_le_mul_left 10 hcx
    have h10X : 10 * X ≤ X ^ 4 := by
      have h83 : 10 ≤ X ^ 3 := by
        calc 10 ≤ 8 ^ 3 := by decide
          _ ≤ X ^ 3 := Nat.pow_le_pow_left hX8 3
      calc 10 * X ≤ X ^ 3 * X := Nat.mul_le_mul_right X h83
        _ = X ^ 4 := by ring
    have hX4_lt : X ^ 4 < 2 ^ w :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by decide : 4 ≤ 24)) hX24
    omega
  have hsubdiv_cw : cw_cs * (Nat.log 2 ((n + 2 * m) + 3 * m + 2) + 1) ≤ w := by
    have h5X : (n + 2 * m) + 3 * m + 2 ≤ 5 * X := by dsimp [X]; omega
    have h5lt : (n + 2 * m) + 3 * m + 2 < 2 ^ (Nat.log 2 X + 4) := by
      calc (n + 2 * m) + 3 * m + 2 ≤ 5 * X := h5X
        _ < 8 * 2 ^ (Nat.log 2 X + 1) := by omega
        _ = 2 ^ 3 * 2 ^ (Nat.log 2 X + 1) := by norm_num
        _ = 2 ^ (Nat.log 2 X + 4) := by rw [← pow_add]; ring_nf
    have hlog_lt : Nat.log 2 ((n + 2 * m) + 3 * m + 2) < Nat.log 2 X + 4 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr h5lt
    have hlog3 : 3 ≤ Nat.log 2 X :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by dsimp [X]; omega)
    have hlog_le : Nat.log 2 ((n + 2 * m) + 3 * m + 2) + 1 ≤ 2 * (Nat.log 2 X + 1) := by omega
    calc cw_cs * (Nat.log 2 ((n + 2 * m) + 3 * m + 2) + 1)
        ≤ cw_cs * (2 * (Nat.log 2 X + 1)) := Nat.mul_le_mul_left cw_cs hlog_le
      _ ≤ (4 * cw_cs + 8) * (Nat.log 2 X + 1) := by nlinarith
      _ ≤ w := hcw_cs
  exact ⟨hd_ge1, hd_le, hX24, hX4, hsubdiv_cw, hKγ_lt, hc_lt, hq_lt, h10c_lt⟩

lemma csTotal_subdiv_le_initSpace {Kγ c K_int cw_cs M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} (hV : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) (phiNum phiDen : ℕ) :
    hdrSize + 2 + 6 * G.m + G.n + Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) ≤
      (pathDSParams Kγ c K_int cw_cs).initSpace phiNum phiDen G.n G.m M := by
  have hcs := @csTotal_subdiv_le_csExpFactor Kγ c K_int cw_cs K hK G M hV hm hmM hnoIso
  have hce : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    csExpFactor_le_gExpImpl Kγ c K_int _ _
  have hmul : 4 * K_int * G.m * csExpFactor Kγ K_int M ≤
      4 * K_int * (G.m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M := by
    have hm1 : G.m ≤ G.m + 1 := by omega
    have h1 : 4 * K_int * G.m ≤ 4 * K_int * (G.m + 1) := Nat.mul_le_mul_left _ hm1
    exact Nat.mul_le_mul h1 hce
  have hcs_le : Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) ≤
      4 * K_int * (G.m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    le_trans hcs hmul
  dsimp only [pathDSParams, hdrSize]
  have hlin : 18 + 2 + 6 * G.m + G.n ≤ 6 * G.n + 30 * G.m + 50 := by omega
  omega

lemma fbInit_space_le_initSpace {Kγ c K_int cw_cs : ℕ}
    {G : Cited.Graph} (phiNum phiDen M : ℕ) :
    let G_s := subdivGraph G
    hdrSize + 2 + 6 * G.m + G.n + (2 * G_s.n + 1 + 4 * G_s.m) + G_s.n + G_s.n + G_s.m ≤
      (pathDSParams Kγ c K_int cw_cs).initSpace phiNum phiDen G.n G.m M := by
  dsimp only [pathDSParams, hdrSize]
  rw [subdivGraph_n, subdivGraph_m]
  have h1 : 18 + 2 + 6 * G.m + G.n + (2 * (G.n + 2 * G.m) + 1 + 4 * (3 * G.m)) +
      (G.n + 2 * G.m) + (G.n + 2 * G.m) + 3 * G.m ≤ 6 * G.n + 30 * G.m + 50 := by omega
  omega

lemma csDel_space_le_delSpace {Kγ c K_int cw_cs M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} (hV : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) (phiNum phiDen : ℕ) :
    G.n + 2 + Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) ≤
      (pathDSParams Kγ c K_int cw_cs).delSpace phiNum phiDen G.n G.m M := by
  have hcs := @csTotal_subdiv_le_csExpFactor Kγ c K_int cw_cs K hK G M hV hm hmM hnoIso
  have hce : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    csExpFactor_le_gExpImpl Kγ c K_int _ _
  have hmul : 4 * K_int * G.m * csExpFactor Kγ K_int M ≤
      4 * K_int * (G.m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M := by
    have h1 : 4 * K_int * G.m ≤ 4 * K_int * (G.m + 1) := Nat.mul_le_mul_left _ (by omega)
    exact Nat.mul_le_mul h1 hce
  have hcs_le : Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) ≤
      4 * K_int * (G.m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    le_trans hcs hmul
  dsimp only [pathDSParams]
  have hlin : G.n + 2 ≤ 100 * (G.n + G.m + 1) + 4000 * phiDen * (G.m + 2) := by omega
  omega

lemma pruneWorkSpace_subdiv_le_delSpace {Kγ c K_int cw_cs : ℕ}
    {G : Cited.Graph} (phiNum phiDen M : ℕ) (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen) (hm : 1 ≤ G.m) :
    let G_s := subdivGraph G
    let d := (phiDen + phiNum - 1) / phiNum
    let C_cap := 40 * d + 1
    let H := 4 * C_cap * (Nat.log 2 (2 * G_s.m + 1) + 1) + 2
    G.n + 2 + pruneWorkSpace G_s.n G_s.m H + 2 ≤
      (pathDSParams Kγ c K_int cw_cs).delSpace phiNum phiDen G.n G.m M := by
  dsimp only [pruneWorkSpace, pathDSParams]
  rw [subdivGraph_n, subdivGraph_m]
  set d := (phiDen + phiNum - 1) / phiNum
  have hd_le : d ≤ phiDen := ceil_div_le_den hpn hpd
  have hlog_le : Nat.log 2 (2 * (3 * G.m) + 1) + 1 ≤ 6 * (G.m + 2) := by
    have hlt : Nat.log 2 (2 * (3 * G.m) + 1) < 2 * (3 * G.m) + 1 :=
      Nat.log_lt_self 2 (by omega)
    omega
  have hH_le : 2 * (4 * (40 * d + 1) * (Nat.log 2 (2 * (3 * G.m) + 1) + 1) + 2) ≤
      4000 * phiDen * (G.m + 2) := by
    have h1 : 40 * d + 1 ≤ 41 * phiDen := by
      have : 1 ≤ phiDen := by omega
      nlinarith
    have hmul : (40 * d + 1) * (Nat.log 2 (2 * (3 * G.m) + 1) + 1) ≤
        (41 * phiDen) * (6 * (G.m + 2)) := Nat.mul_le_mul h1 hlog_le
    nlinarith
  have hlin : G.n + 2 + (12 * (G.n + 2 * G.m) + 3 * G.m + 2) + 2 ≤ 100 * (G.n + G.m + 1) := by omega
  omega

lemma nat_log_add_two_le_gExp (Kγ c K_int d M : ℕ) :
    Nat.log 2 (M + 2) + 1 ≤ gExpImpl Kγ c K_int d M := by
  set q := qRoot M + 1
  have h1 : Nat.log 2 (M + 2) + 1 ≤ q ^ 8 := log_lt_succ_qRoot_pow_eight M
  have h2 : q ^ 8 ≤ 2 ^ (q ^ 7 + 2) := by
    by_cases hq1 : q = 1
    · rw [hq1]; decide
    · have hq2 : 2 ≤ q := by dsimp [q]; omega
      have h8q : 8 * q ≤ q ^ 7 + 2 := by
        have hq6 : 64 ≤ q ^ 6 := le_trans (by decide : 64 ≤ 2 ^ 6) (Nat.pow_le_pow_left hq2 6)
        have hmul : 8 * q ≤ q ^ 6 * q :=
          le_trans (Nat.mul_le_mul_right q (by decide : 8 ≤ 64)) (Nat.mul_le_mul_right q hq6)
        have hpow7 : q ^ 6 * q = q ^ 7 := by ring
        omega
      have hql : q < 2 ^ q := Nat.lt_two_pow_self
      calc q ^ 8 ≤ (2 ^ q) ^ 8 := Nat.pow_le_pow_left hql.le 8
        _ = 2 ^ (8 * q) := by rw [← pow_mul, mul_comm]
        _ ≤ 2 ^ (q ^ 7 + 2) := Nat.pow_le_pow_right (by decide) h8q
  have hqp : qExpPow M = q ^ 7 + 2 := by unfold qExpPow; rfl
  have h2' : q ^ 8 ≤ 2 ^ qExpPow M := hqp ▸ h2
  have h3 : 2 ^ qExpPow M ≤ csExpFactor Kγ K_int M := by
    unfold csExpFactor
    exact le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)) (Nat.le_add_right _ _)
  have h4 : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int d M :=
      csExpFactor_le_gExpImpl Kγ c K_int _ _
  omega

lemma pruneWordBound_subdiv_val_lt {Kγ c K_int cw_cs w phiNum phiDen n m M : ℕ}
    (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hKγ : 1 ≤ Kγ) (hc : 1 ≤ c) (hK1 : 1 ≤ K_int) (hKγ_le : Kγ ≤ K_int)
    (hw : (pathDSParams Kγ c K_int cw_cs).cw *
      (Nat.log 2 (n + m + phiDen + M +
        Nat.ceil ((pathDSParams Kγ c K_int cw_cs).γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M) + 2) + 1) ≤ w) :
    let d := (phiDen + phiNum - 1) / phiNum
    let C_cap := 40 * d + 1
    let H := 4 * C_cap * (Nat.log 2 (2 * (3 * m) + 1) + 1) + 2
    8 * C_cap * (3 * m) + 4 * C_cap + 2 * (n + 2 * m) + 2 * (3 * m) + H + 16 < 2 ^ w := by
  have hcw := cw_world_bounds hpn hpd hm hmM hKγ hc hK1 hKγ_le hw
  rcases hcw with ⟨_, hd_le, hX24, _, _, _, _, _, _⟩
  set d := (phiDen + phiNum - 1) / phiNum
  set X := n + m + phiDen + M + gExpImpl Kγ c K_int d M + 2
  set C_cap := 40 * d + 1
  set H := 4 * C_cap * (Nat.log 2 (2 * (3 * m) + 1) + 1) + 2
  have hX7 : 7 ≤ X := by
    have hg2 : 2 ≤ gExpImpl Kγ c K_int d M :=
      two_le_gExpImpl Kγ c K_int _ _
    dsimp [X]; omega
  have hC_le : C_cap ≤ 41 * phiDen := by
    have : 1 ≤ phiDen := by omega
    dsimp [C_cap]; nlinarith
  have hC_X : C_cap ≤ 41 * X := by
    have : phiDen ≤ X := by dsimp [X]; omega
    nlinarith
  have hm_X : m ≤ X := by dsimp [X]; omega
  have hlog_le : Nat.log 2 (2 * (3 * m) + 1) + 1 ≤ 6 * m + 2 := by
    have hlt := Nat.log_lt_self 2 (by omega : 2 * (3 * m) + 1 ≠ 0)
    omega
  have hlog_X : Nat.log 2 (2 * (3 * m) + 1) + 1 ≤ 8 * X := by omega
  have hH_X2 : H ≤ 1312 * (X * X) + 2 := by
    have hmul : C_cap * (Nat.log 2 (2 * (3 * m) + 1) + 1) ≤ (41 * X) * (8 * X) :=
      Nat.mul_le_mul hC_X hlog_X
    have h4 : (41 * X) * (8 * X) = 328 * (X * X) := by ring
    have hassoc : 4 * C_cap * (Nat.log 2 (2 * (3 * m) + 1) + 1) =
        4 * (C_cap * (Nat.log 2 (2 * (3 * m) + 1) + 1)) := mul_assoc _ _ _
    dsimp [H]
    omega
  have hCm : C_cap * m ≤ 41 * (X * X) := by
    have hmul := Nat.mul_le_mul hC_X hm_X
    have h1 : (41 * X) * X = 41 * (X * X) := by ring
    omega
  have hX_le_X2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hval_X2 : 8 * C_cap * (3 * m) + 4 * C_cap + 2 * (n + 2 * m) + 2 * (3 * m) + H + 16 ≤
      3000 * (X * X) := by
    have h1 : 8 * C_cap * (3 * m) = 24 * (C_cap * m) := by ring
    have h2 : 2 * (n + 2 * m) + 2 * (3 * m) ≤ 10 * X := by dsimp [X]; omega
    omega
  have h3000 : 3000 * (X * X) < X ^ 24 := by
    have hpow22 : 3000 < X ^ 22 := by
      have h7_5 : 3000 < 7 ^ 5 := by decide
      have hX5 : 7 ^ 5 ≤ X ^ 5 := Nat.pow_le_pow_left hX7 5
      have h5_22 : X ^ 5 ≤ X ^ 22 := Nat.pow_le_pow_right (by omega) (by decide)
      omega
    have hsq : X * X = X ^ 2 := (sq X).symm
    have hmul : 3000 * X ^ 2 < X ^ 22 * X ^ 2 :=
      Nat.mul_lt_mul_of_pos_right hpow22 (Nat.pow_pos (by omega))
    have hpow24 : X ^ 22 * X ^ 2 = X ^ 24 := (pow_add X 22 2).symm
    omega
  exact lt_trans (lt_of_le_of_lt hval_X2 h3000) hX24

lemma subdivGraph_degIn_verts {G : Cited.Graph} (hV : G.IsValid) {v : ℕ}
    (_hv : v < (subdivGraph G).n) :
    1 ≤ (subdivGraph G).degIn (subdivGraph G).verts v ↔ 1 ≤ (subdivGraph G).deg v := by
  have hSV := subdivGraph_isValid hV
  simp [Cited.Graph.degIn, Cited.Graph.deg, inside_verts_of_isValid hSV]

lemma csQuery_space_le_querySpace {Kγ c K_int cw_cs M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} (hmM : G.m ≤ M) (phiNum phiDen : ℕ) :
    2 * G.n + 4 + Cited.csQuery Kγ K (3 * G.m) (qOf M) ≤
      (pathDSParams Kγ c K_int cw_cs).querySpace phiNum phiDen G.n G.m M := by
  have hcq := csQuery_subdiv_le_csExpFactor (Kγ := Kγ) (K_int := K_int) hK (by omega : 3 * G.m ≤ 4 * M)
  have hce : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    csExpFactor_le_gExpImpl Kγ c K_int _ _
  have hmul : Cited.csQuery Kγ K (3 * G.m) (qOf M) ≤
      2 * K_int * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M :=
    le_trans hcq (Nat.mul_le_mul_left (2 * K_int) hce)
  dsimp only [pathDSParams]
  have hlin : 2 * G.n + 4 ≤ 20 * (G.n + G.m + 1) := by omega
  omega

lemma fbQuery_space_le_querySpace {Kγ c K_int cw_cs : ℕ}
    {G : Cited.Graph} (phiNum phiDen M : ℕ) :
    2 * G.n + 4 + 6 * (subdivGraph G).n + 2 ≤
      (pathDSParams Kγ c K_int cw_cs).querySpace phiNum phiDen G.n G.m M := by
  dsimp only [pathDSParams]
  rw [subdivGraph_n]
  omega

lemma csGamma_rpow_le_gExp {Kγ c K_int M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {m d : ℕ} (hmM : 3 * m ≤ 4 * M) :
    (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) ≤
      (gExpImpl Kγ c K_int d M : ℝ) := by
  have hK_le : K ≤ (K_int : ℝ) := le_trans (le_max_left K 1) hK
  have hK1 : 1 ≤ K_int := by exact_mod_cast (le_trans (le_max_right K 1) hK)
  have hcs_le_exp : (csExpFactor Kγ K_int M : ℝ) ≤ (gExpImpl Kγ c K_int d M : ℝ) := by
    exact_mod_cast (csExpFactor_le_gExpImpl Kγ c K_int d M)
  by_cases hK0 : K ≤ 0
  · have hge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := by
      exact_mod_cast (by rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ 2 (by decide))
    have hexp_le0 : K * (qOf M : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK0 (Nat.cast_nonneg _)
    have hrpow1 : (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hge1 hexp_le0
    have h1_le_cs : (1 : ℝ) ≤ (csExpFactor Kγ K_int M : ℝ) := by
      exact_mod_cast (by unfold csExpFactor; exact Nat.le_add_left 1 _)
    exact le_trans hrpow1 (le_trans h1_le_cs hcs_le_exp)
  · have hK0' : 0 ≤ K := le_of_not_ge hK0
    have hgamma_mono : (Cited.csGamma Kγ (3 * m) : ℝ) ≤ (Cited.csGamma Kγ (4 * M) : ℝ) := by
      exact_mod_cast csGamma_mono hmM
    have hge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (4 * M) : ℝ) := by
      exact_mod_cast (by rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ 2 (by decide))
    have hpow_kq : K * (qOf M : ℝ) ≤ ((K_int * qOf M : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg _)
    set A := csGammaExp Kγ (4 * M) * K_int * qOf M
    set E := A + qExpPow M
    have hcs_nn : (0 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := Nat.cast_nonneg _
    have hrpow_E : (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) ≤ ((2 ^ E : ℕ) : ℝ) := by
      have hcast_A : (Cited.csGamma Kγ (4 * M) : ℝ) ^ ((K_int * qOf M : ℕ) : ℝ) = ((2 ^ A : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, csGamma_eq_two_pow]
        have hmul : (2 ^ csGammaExp Kγ (4 * M)) ^ (K_int * qOf M) = 2 ^ A := by
          rw [← pow_mul, ← mul_assoc]
        exact_mod_cast hmul
      calc (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ))
          ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K * (qOf M : ℝ)) :=
            Real.rpow_le_rpow hcs_nn hgamma_mono (mul_nonneg hK0' (Nat.cast_nonneg _))
        _ ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ ((K_int * qOf M : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 hpow_kq
        _ = ((2 ^ A : ℕ) : ℝ) := hcast_A
        _ ≤ ((2 ^ E : ℕ) : ℝ) := by
            exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_add_right A (qExpPow M))
    have hE_le : ((2 ^ E : ℕ) : ℝ) ≤ (csExpFactor Kγ K_int M : ℝ) := by
      exact_mod_cast (Nat.le_add_right (2 ^ E) 1 : 2 ^ E ≤ csExpFactor Kγ K_int M)
    exact le_trans hrpow_E (le_trans hE_le hcs_le_exp)

lemma initCost_ge_cs_total {Kγ c K_int cw_cs M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} (hV : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) {phiNum phiDen : ℕ} (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen) :
    2 * Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) +
        (4000 * G.m + 2000) ≤
      Nat.ceil ((pathDSParams Kγ c K_int cw_cs).K_init * (G.m : ℝ) *
        (pathDSParams Kγ c K_int cw_cs).γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M) := by
  set d := (phiDen + phiNum - 1) / phiNum
  set p := pathDSParams Kγ c K_int cw_cs
  have hceil_d : Nat.ceil (1 / ((phiNum : ℝ) / (phiDen : ℝ))) = d := nat_ceil_div_eq hpn hpd
  have hγ_eq : p.γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M = (gExpImpl Kγ c K_int d M : ℝ) := by
    unfold PathDSParams.γ_ExpPath; dsimp [p, pathDSParams]; rw [hceil_d]
  have hcs := @csTotal_subdiv_le_csExpFactor Kγ c K_int cw_cs K hK G M hV hm hmM hnoIso
  have hce : csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int d M :=
      csExpFactor_le_gExpImpl Kγ c K_int _ _
  have hg2 : 2 ≤ gExpImpl Kγ c K_int d M :=
      two_le_gExpImpl Kγ c K_int _ _
  have hcs_g : Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) ≤
      4 * K_int * G.m * gExpImpl Kγ c K_int d M :=
    le_trans hcs (Nat.mul_le_mul_left _ hce)
  have hrem : 4000 * G.m + 2000 ≤ 4000 * G.m * gExpImpl Kγ c K_int d M := by
    have h1 : 4000 * G.m + 2000 ≤ 4000 * G.m * 2 := by omega
    have h2 : 4000 * G.m * 2 ≤ 4000 * G.m * gExpImpl Kγ c K_int d M :=
      Nat.mul_le_mul_left _ hg2
    omega
  have hnat : 2 * Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) +
      (4000 * G.m + 2000) ≤ (10 * K_int + 4000) * G.m * gExpImpl Kγ c K_int d M := by
    have hsum : (8 * K_int * G.m + 4000 * G.m) * gExpImpl Kγ c K_int d M ≤
        (10 * K_int + 4000) * G.m * gExpImpl Kγ c K_int d M := by
      have hcoef : 8 * K_int * G.m + 4000 * G.m ≤ (10 * K_int + 4000) * G.m := by
        have : 8 * K_int * G.m + 4000 * G.m = (8 * K_int + 4000) * G.m := by ring
        rw [this]
        exact Nat.mul_le_mul_right G.m (by omega)
      exact Nat.mul_le_mul_right _ hcoef
    calc 2 * Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) + (4000 * G.m + 2000)
        ≤ 2 * (4 * K_int * G.m * gExpImpl Kγ c K_int d M) + 4000 * G.m * gExpImpl Kγ c K_int d M :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 hcs_g) hrem
      _ = (8 * K_int * G.m + 4000 * G.m) * gExpImpl Kγ c K_int d M := by ring
      _ ≤ (10 * K_int + 4000) * G.m * gExpImpl Kγ c K_int d M := hsum
  have hpK : p.K_init = 10 * (K_int : ℝ) + 4000 := rfl
  exact nat_le_ceil_of_cast_le (by rw [hγ_eq, hpK]; exact_mod_cast hnat)

end MinCostFlow.Expander.PathDSProg
