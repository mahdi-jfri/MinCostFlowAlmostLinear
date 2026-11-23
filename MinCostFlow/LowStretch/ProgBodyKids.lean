module

public import MinCostFlow.LowStretch.ProgBody
public import MinCostFlow.LowStretch.ProgRecFrame

/-!
# The end of the node part: from the child step to `BodyPost`

The node part calls the child step with a heap pointer `h'` above all it wrote itself. The child
step leaves the record blocks of the children at `h' + 9k` and the end `v` of its heap
(`ChildPost`). Then the node part writes four words at `h`: the number of children, the address
`h'` of their record blocks, the end `v` of the heap and the address `PT` of the portals
(`wr4`). `bodyPost_of_child` shows that the memory then meets `BodyPost`, when the portals were
written at `PT` before the child step, and the cost and the heap fit.

The four words lie between the cells below `h` (the global arrays, the labels and the local
indices) and the cells from `h + 4` on (the portals and all that the child step wrote). So they
change nothing that a record block of a child reads (`RecAt.congr`).

`childPre_of` gives the precondition of the child step from `ClPre`, when the memory still agrees
with `mem` below `h`, and the petal block and its arrays lie between `h` and `h'`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par}

/-- The memory `M` with the four words `x0, x1, x2, x3` at `h, …, h + 3`. -/
def wr4 (M : ℕ → ℕ) (h x0 x1 x2 x3 : ℕ) : ℕ → ℕ := fun a =>
  if a = h then x0 else if a = h + 1 then x1 else if a = h + 2 then x2 else if a = h + 3 then x3
  else M a

theorem wr4_out {M : ℕ → ℕ} {h x0 x1 x2 x3 a : ℕ} (ha : a < h ∨ h + 4 ≤ a) :
    wr4 M h x0 x1 x2 x3 a = M a := by
  simp [wr4, show a ≠ h by omega, show a ≠ h + 1 by omega, show a ≠ h + 2 by omega,
    show a ≠ h + 3 by omega]

/-- Four stores at `h, h + 1, h + 2, h + 3`, in this order, give `wr4`. -/
theorem wr4_eq (M : ℕ → ℕ) (h x0 x1 x2 x3 : ℕ) :
    Function.update (Function.update (Function.update (Function.update M h x0) (h + 1) x1)
      (h + 2) x2) (h + 3) x3 = wr4 M h x0 x1 x2 x3 := by
  funext a
  simp only [Function.update_apply, wr4]
  by_cases h0 : a = h
  · subst h0; simp
  by_cases h1 : a = h + 1
  · subst h1; simp
  by_cases h2 : a = h + 2
  · subst h2; simp
  by_cases h3 : a = h + 3
  · subst h3; simp
  simp [h0, h1, h2, h3]

/-- **From the child step to `BodyPost`.** The memory `M1` before the child step agrees with
`mem` below `h` and holds the portals at `PT`. The child step, called at `h'`, leaves `M2`, the
children `cs` with records `Rs` and the end `v` of the heap, as `ChildPost` says. With the four
words at `h`, the memory meets `BodyPost`. The stored-pair bound `hS` (the last part of `ChildPost`),
the heap bound `hheap` and the cost bound `hcost` are hypotheses. -/
theorem bodyPost_of_child {w A : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec} {cs : ℕ → Cl}
    {Rs : ℕ → Rec} {GB RB h h' PT v cost : ℕ} {mem M1 M2 : ℕ → ℕ}
    (hpre : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D)
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X)
    (hlow : ∀ a < h, M1 a = mem a) (hh' : h + 4 ≤ h') (hPT : h + 4 ≤ PT)
    (hPT2 : PT + D.ps.length ≤ h') (hport : ∀ j < D.ps.length, M1 (PT + j) = D.portal j)
    (hk : ∀ k < D.nch, Next G P (c.raw G D k) (cs k) ∧ (Rs k).Ok T G P (cs k) ∧
      RecAt T G (cs k) (Rs k) (GlobL.read mem GB) (RecL.read M2 (h' + 9 * k)) M2 ∧
      ∀ r ∈ (RecL.read M2 (h' + 9 * k)).regs, h' + 9 * D.nch ≤ r.1 ∧ r.1 + r.2 ≤ v)
    (hv : h' + 9 * D.nch ≤ v) (hz : ZeroFrom M2 v)
    (hfr : ∀ a < h', ¬ ChildWr T G c (GlobL.read mem GB) a → M2 a = M1 a)
    (hlab : ∀ x < G.n, M1 ((GlobL.read mem GB).LAB + x) < T.N →
      M2 ((GlobL.read mem GB).LAB + x) < T.N)
    (hloc : ∀ x < T.N, M2 ((GlobL.read mem GB).LOC + x) = M1 ((GlobL.read mem GB).LOC + x) ∨
      M2 ((GlobL.read mem GB).LOC + x) < T.N)
    (hS : ∑ k ∈ Finset.range D.nch, (Rs k).S.length ≤
      (c.act G P).card + ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ)
    (hheap : v ≤ h + 4 + ((GlobL.read mem GB).J + 1) *
      (bodyShare A T G P c R D cs + D.nch * kidCost w G.n))
    (hcost : cost ≤ bodyShare A T G P c R D cs + D.nch * kidCost w G.n) :
    BodyPost w A T G P c R (GlobL.read mem GB) h mem (wr4 M2 h D.nch h' v PT) cost := by
  have hT := hpre.glob.tree
  have hsub := hpre.ok.sub
  have hθ := hpre.ok.inv.one_le
  have hlb := hpre.lab_below
  have hlc := hpre.loc_below
  obtain ⟨Mw, -, -, hroom⟩ := hpre.room_sq
  have hNw : T.N < 2 ^ w := by
    have h1 : T.N + G.m + 2 ≤ (T.N + G.m + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2 : 1 ≤ 2 ^ (2 * (GlobL.read mem GB).J + 20) := Nat.one_le_two_pow
    have h3 : 1 ≤ (Mw + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul (Nat.mul_le_mul h2 h1) h3
    simp only [one_mul, mul_one] at this
    omega
  -- the cells below `h` that are read and are not labels or local indices
  have hkeep : ∀ a < h, ¬ ChildWr T G c (GlobL.read mem GB) a → wr4 M2 h D.nch h' v PT a = mem a := fun a ha hn => by
    rw [wr4_out (Or.inl ha), hfr a (by omega) hn, hlow a ha]
  have hglob : (GlobL.read mem GB).Ok T G P M2 := by
    refine hpre.glob.congr (fun r hr i hi => ?_)
    have hr' : r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB) := mem_recRegs.mpr (Or.inr (Or.inr (Or.inl hr)))
    have hb := hpre.below r hr'
    have hn := not_childWr (a := r.1 + i) hT hsub hθ (hpre.lab_disj r hr') (hpre.loc_disj r hr')
      (by omega) (by omega)
    rw [hfr _ (by omega) hn, hlow _ (by omega)]
  refine ⟨hkeep, fun u hu => ?_, fun x hx => ?_, ?_, fun a ha => ?_, Or.inr ⟨D, cs, Rs, hX, hD,
    ⟨?_, fun k hkn => ?_, ?_, ?_, fun j hj => ?_⟩, hS, ?_, hcost⟩⟩
  · rw [wr4_out (Or.inl (by omega))]
    exact hlab u hu (by rw [hlow _ (by omega)]; exact hpre.lab_lt u hu)
  · rw [wr4_out (Or.inl (by omega))]
    rcases hloc x hx with e | e
    · rw [e, hlow _ (by omega)]; exact hpre.loc_w x hx
    · omega
  · simp [wr4]; omega
  · have hva : v ≤ a := by simpa [wr4] using ha
    rw [wr4_out (Or.inr (by omega))]
    exact hz a hva
  · simp [wr4]
  · obtain ⟨hn, hok, hat, hregs⟩ := hk k hkn
    have hb1 : wr4 M2 h D.nch h' v PT (h + 1) = h' := by simp [wr4]
    have hb2 : wr4 M2 h D.nch h' v PT (h + 2) = v := by simp [wr4]
    rw [hb1, hb2]
    have hkn' : k + 1 ≤ D.nch := hkn
    have h9 : 9 * k + 9 ≤ 9 * D.nch := by omega
    have hL : RecL.read (wr4 M2 h D.nch h' v PT) (h' + 9 * k) = RecL.read M2 (h' + 9 * k) :=
      RecL.read_congr fun i hi => wr4_out (Or.inr (by omega))
    rw [hL]
    refine ⟨hn, hsat k hkn, hok, ?_, by omega, by omega, fun r hr => ?_⟩
    · have hsubk := hok.sub
      have hθk := hok.inv.one_le
      refine RecAt.congr (GB := GB) (RB := h' + 9 * k) hglob hat (fun r hr i hi => ?_)
        (fun u hu => ?_) (fun u hu => ?_)
      · rcases mem_recRegs.mp hr with rfl | rfl | hg | hl
        · have := hpre.below (GB, 21) (by simp [recRegs])
          exact wr4_out (Or.inl (by simp only at this hi ⊢; omega))
        · exact wr4_out (Or.inr (by simp only at hi ⊢; omega))
        · have := hpre.below r (mem_recRegs.mpr (Or.inr (Or.inr (Or.inl hg))))
          exact wr4_out (Or.inl (by omega))
        · have := (hregs r hl).1
          exact wr4_out (Or.inr (by omega))
      · have := Finset.mem_range.mp (hsubk hu)
        exact wr4_out (Or.inl (by omega))
      · have hun := Finset.mem_range.mp (hsubk hu)
        have htop := KT.top_lt_N hT hun hθk
        have := (KT.hd_under hT _ htop).lt_N hT htop
        exact wr4_out (Or.inl (by omega))
    · have := hregs r hr
      exact ⟨by omega, this.2⟩
  · simp [wr4]; omega
  · simp [wr4]; omega
  · simp only [show wr4 M2 h D.nch h' v PT (h + 3) = PT by simp [wr4]]
    rw [wr4_out (Or.inr (by omega))]
    have hn : ¬ ChildWr T G c (GlobL.read mem GB) (PT + j) := by
      intro hw
      rcases ChildWr.cell hT hsub hθ hw with ⟨u, hu, e⟩ | ⟨x, hx, e⟩ <;> omega
    rw [hfr _ (by omega) hn]
    exact hport j hj
  · simp only [show wr4 M2 h D.nch h' v PT (h + 2) = v by simp [wr4]]
    exact hheap

/-- **From `ChildPost` to `BodyPost`.** The same as `bodyPost_of_child`, with the parts of the
child step taken from `ChildPost` (its last part is the stored-pair bound). The cost `cost` of the
node part and the heap bound are asked for every choice of the children whose cost bound
`ChildPost` gives (`hfit`). -/
theorem bodyPost_of_childPost {w A : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec}
    {GB RB h h' PT v cost cost' : ℕ} {mem M1 M2 : ℕ → ℕ}
    (hpre : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D)
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X)
    (hlow : ∀ a < h, M1 a = mem a) (hh' : h + 4 ≤ h') (hPT : h + 4 ≤ PT)
    (hPT2 : PT + D.ps.length ≤ h') (hport : ∀ j < D.ps.length, M1 (PT + j) = D.portal j)
    (hE : GlobL.read M1 GB = GlobL.read mem GB)
    (hpost : ChildPost T G P c R D (GlobL.read M1 GB) h' M1 v M2 cost')
    (hfit : ∀ cs : ℕ → Cl, cost' ≤ childCost T G P c R D cs (GlobL.read mem GB).J →
      cost ≤ bodyShare A T G P c R D cs + D.nch * kidCost w G.n ∧
      h' + ((GlobL.read mem GB).J + 1) * childCost T G P c R D cs (GlobL.read mem GB).J ≤
        h + 4 + ((GlobL.read mem GB).J + 1) *
          (bodyShare A T G P c R D cs + D.nch * kidCost w G.n)) :
    BodyPost w A T G P c R (GlobL.read mem GB) h mem (wr4 M2 h D.nch h' v PT) cost := by
  rw [hE] at hpost
  obtain ⟨cs, Rs, hk, hv, hz, hfr, hheap, hcost, hlab, hloc, hS⟩ := hpost
  obtain ⟨f1, f2⟩ := hfit cs hcost
  exact bodyPost_of_child hpre hX hD hsat hlow hh' hPT hPT2 hport hk hv hz hfr hlab hloc hS
    (by omega) f1

/-! ### The precondition of the child step -/

theorem mem_readRegs {GB RB XB : ℕ} {E : GlobL} {L : RecL} {X : PetL} {M : ℕ → ℕ} {r : ℕ × ℕ} :
    r ∈ readRegs GB RB XB E L X M ↔
      r ∈ recRegs GB RB E L ∨ r = (XB, 16) ∨ r ∈ X.regs M L.s := by
  simp only [readRegs, recRegs_eq, globArrs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false]
  tauto

/-- **The precondition of the child step**, called at `h'` with the petal block at `XB`, on a
memory `M1` that agrees with `mem` below `h`. The petal block and its arrays lie in
`[h, h')`, and the memory is zero from `h'` on. -/
theorem childPre_of {w A : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec} {GB RB XB h h' : ℕ}
    {mem M1 : ℕ → ℕ} (hpre : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) (hlow : ∀ a < h, M1 a = mem a)
    (hpet : (PetL.read M1 XB).Ok T G P c R D M1) (hXB : h ≤ XB) (hXB2 : XB + 16 ≤ h')
    (hregs : ∀ r ∈ (PetL.read M1 XB).regs M1 (RecL.read mem RB).s, h ≤ r.1 ∧ r.1 + r.2 ≤ h')
    (hz : ZeroFrom M1 h')
    (hroom : ∃ Mw, (∀ p < G.m, G.pω p ≤ Mw) ∧ (GlobL.read mem GB).INF ≤ 4 * G.n * Mw + 4 ∧
      h' + 2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 < 2 ^ w) :
    ChildPre w T G P c R D GB RB XB h' M1 := by
  have hT := hpre.glob.tree
  have hsub := hpre.ok.sub
  have hθ := hpre.ok.inv.one_le
  have hlb := hpre.lab_below
  have hlc := hpre.loc_below
  have hbelow := hpre.below
  have hG : GlobL.read M1 GB = GlobL.read mem GB := GlobL.read_congr fun i hi => by
    have := hbelow (GB, 21) (by simp [recRegs]); simp only at this
    exact hlow _ (by omega)
  have hR : RecL.read M1 RB = RecL.read mem RB := RecL.read_congr fun i hi => by
    have := hbelow (RB, 9) (by simp [recRegs]); simp only at this
    exact hlow _ (by omega)
  have hsame : ∀ rs : List (ℕ × ℕ), (∀ r ∈ rs, r.1 + r.2 ≤ h) → SameOn rs mem M1 :=
    fun rs hrs r hr i hi => by have := hrs r hr; exact hlow _ (by omega)
  have hrec : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hbelow
  have hglob : (GlobL.read mem GB).Ok T G P M1 :=
    hpre.glob.congr (hsame _ fun r hr =>
      hrec r (mem_recRegs.mpr (Or.inr (Or.inr (Or.inl hr)))))
  have hat : RecAt T G c R (GlobL.read mem GB) (RecL.read mem RB) M1 :=
    RecAt.congr (GB := GB) (RB := RB) hpre.glob hpre.recAt (hsame _ hrec)
      (fun v hv => by have := Finset.mem_range.mp (hsub hv); exact hlow _ (by omega))
      (fun v hv => by
        have hvn := Finset.mem_range.mp (hsub hv)
        have htop := KT.top_lt_N hT hvn hθ
        have := (KT.hd_under hT _ htop).lt_N hT htop
        exact hlow _ (by omega))
  have hup : ∀ r ∈ readRegs GB RB XB (GlobL.read mem GB) (RecL.read mem RB) (PetL.read M1 XB) M1,
      (r.1 + r.2 ≤ h ∧ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB)) ∨
        (h ≤ r.1 ∧ r.1 + r.2 ≤ h') := by
    intro r hr
    rcases mem_readRegs.mp hr with h1 | rfl | h3
    · exact Or.inl ⟨hrec r h1, h1⟩
    · exact Or.inr ⟨hXB, hXB2⟩
    · exact Or.inr (hregs r h3)
  refine ⟨hX, hpre.ok, hD, by rw [hG]; exact hglob, by rw [hG, hR]; exact hat, hpet, hz,
    fun r hr => ?_, by rw [hG]; omega, by rw [hG]; omega, by rw [hG]; exact hpre.lab_loc,
    fun r hr => ?_, fun r hr => ?_, by rw [hG]; exact hroom, fun v hv => ?_, fun x hx => ?_⟩
  · rw [hG, hR] at hr
    rcases hup r hr with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
  · rw [hG, hR] at hr
    rw [hG]
    rcases hup r hr with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hpre.lab_disj r h2
    · exact Or.inr (by simp only; omega)
  · rw [hG, hR] at hr
    rw [hG]
    rcases hup r hr with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hpre.loc_disj r h2
    · exact Or.inr (by simp only; omega)
  · rw [hG, hlow _ (by omega)]; exact hpre.lab_lt v hv
  · rw [hG, hlow _ (by omega)]; exact hpre.loc_w x hx

end MinCostFlow.LowStretch
