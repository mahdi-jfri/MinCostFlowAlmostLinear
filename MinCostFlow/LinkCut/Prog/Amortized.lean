module

public import WordRAM.Contract
import WordRAM.Exec

namespace MinCostFlow.LinkCut.Prog

/-!
This file defines amortized contracts for Word-RAM data-structure procedures
and proves the telescoping bound over sequences of operations.

A procedure meets an amortized contract with potential `phi` and amortized bound
`amortCost` if on every valid input state and coin outcome it terminates with
postcondition satisfied and actual step cost `c` satisfying
`c + phi st'.mem ≤ amortCost args mem + phi mem`.
Initialization starts from an uninitialized state and satisfies `c + phi st'.mem ≤ cost args mem`.
-/

open WordRAM

@[expose] public section

/-- Specification of an amortized Word-RAM procedure relative to a potential
`phi : (ℕ → ℕ) → ℕ`. -/
structure AmortizedContract where
  pre : List ℕ → (ℕ → ℕ) → Prop
  post : List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  phi : (ℕ → ℕ) → ℕ
  amortCost : List ℕ → (ℕ → ℕ) → ℕ

/-- Specification of an initializing Word-RAM procedure establishing a potential `phi`. -/
structure InitContract where
  pre : List ℕ → (ℕ → ℕ) → Prop
  post : List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  phi : (ℕ → ℕ) → ℕ
  cost : List ℕ → (ℕ → ℕ) → ℕ

/-- Procedure `f` of program `p` (at word size `w`) meets amortized contract `A`
when every valid input terminates with `A.post` and `c + A.phi st'.mem ≤ A.amortCost args mem + A.phi mem`. -/
def MeetsAmortizedContract (w : ℕ) (p : Program) (f : ℕ) (A : AmortizedContract) : Prop :=
  ∀ args mem pos ω,
    (∀ a ∈ args, a < 2 ^ w) →
    A.pre args mem →
    ∃ body, p.procs[f]? = some body ∧
      ∃ o st' c,
        Runs w p ω body (startState args mem pos) o st' c ∧
        A.post args mem o.value st'.mem ∧
        c + A.phi st'.mem ≤ A.amortCost args mem + A.phi mem

/-- Procedure `f` of program `p` (at word size `w`) meets initialization contract `I`
when every valid input terminates with `I.post` and `c + I.phi st'.mem ≤ I.cost args mem`. -/
def MeetsInitContract (w : ℕ) (p : Program) (f : ℕ) (I : InitContract) : Prop :=
  ∀ args mem pos ω,
    (∀ a ∈ args, a < 2 ^ w) →
    I.pre args mem →
    ∃ body, p.procs[f]? = some body ∧
      ∃ o st' c,
        Runs w p ω body (startState args mem pos) o st' c ∧
        I.post args mem o.value st'.mem ∧
        c + I.phi st'.mem ≤ I.cost args mem

/-- Worst-case `Contract` induced by an `AmortizedContract` with cost `amortCost + phi`. -/
def AmortizedContract.toContract (A : AmortizedContract) : Contract where
  pre := A.pre
  post := A.post
  cost args mem := A.amortCost args mem + A.phi mem

/-- Worst-case `Contract` induced by an `InitContract`. -/
def InitContract.toContract (I : InitContract) : Contract where
  pre := I.pre
  post := I.post
  cost := I.cost

/-- Every amortized contract implies its induced worst-case `Contract`. -/
theorem MeetsAmortizedContract.to_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    {A : AmortizedContract} (h : MeetsAmortizedContract w p f A) :
    MeetsContract w p f A.toContract := by
  intro args mem pos ω hargs hpre
  rcases h args mem pos ω hargs hpre with ⟨body, hproc, o, st', c, hrun, hpost, hcost⟩
  exact ⟨body, hproc, o, st', c, hrun, hpost, Nat.le_trans (Nat.le_add_right _ _) hcost⟩

/-- Every initialization contract implies its induced worst-case `Contract`. -/
theorem MeetsInitContract.to_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    {I : InitContract} (h : MeetsInitContract w p f I) :
    MeetsContract w p f I.toContract := by
  intro args mem pos ω hargs hpre
  rcases h args mem pos ω hargs hpre with ⟨body, hproc, o, st', c, hrun, hpost, hcost⟩
  exact ⟨body, hproc, o, st', c, hrun, hpost, Nat.le_trans (Nat.le_add_right _ _) hcost⟩

/-- A sequence of `t` amortized steps starting at `mem₀` and ending at `memₙ`,
accumulating total actual cost `actualCost` and total amortized cost `amortTotal`. -/
inductive AmortizedTrace (phi : (ℕ → ℕ) → ℕ) :
    (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → ℕ → Prop where
  | nil (mem : ℕ → ℕ) : AmortizedTrace phi mem mem 0 0 0
  | step {mem₀ mem₁ mem₂ : ℕ → ℕ} {t cStep aStep cRest aRest : ℕ} :
      cStep + phi mem₁ ≤ aStep + phi mem₀ →
      AmortizedTrace phi mem₁ mem₂ t cRest aRest →
      AmortizedTrace phi mem₀ mem₂ (t + 1) (cStep + cRest) (aStep + aRest)

/-- Telescoping potential bound for an `AmortizedTrace`: total actual cost plus final
potential is at most total amortized cost plus initial potential. -/
theorem AmortizedTrace.bound {phi : (ℕ → ℕ) → ℕ} {mem₀ memₙ : ℕ → ℕ}
    {t cTotal aTotal : ℕ} (ht : AmortizedTrace phi mem₀ memₙ t cTotal aTotal) :
    cTotal + phi memₙ ≤ aTotal + phi mem₀ := by
  induction ht with
  | nil _ => exact Nat.le_refl _
  | step hstep _ ih => omega

/-- Combining an initialization step with an `AmortizedTrace` removes the potential
completely and bounds total cost by `cInitBound + aTotal`. -/
theorem AmortizedTrace.init_bound {phi : (ℕ → ℕ) → ℕ} {mem₀ memₙ : ℕ → ℕ}
    {cInit cInitBound t cTotal aTotal : ℕ}
    (hinit : cInit + phi mem₀ ≤ cInitBound)
    (ht : AmortizedTrace phi mem₀ memₙ t cTotal aTotal) :
    cInit + cTotal ≤ cInitBound + aTotal := by
  have hb := ht.bound
  omega

/-- If every operation in an `AmortizedTrace` has amortized cost at most `stepBound`,
then the total actual cost of `t` operations is at most `t * stepBound + phi mem₀`. -/
inductive BoundedAmortizedTrace (phi : (ℕ → ℕ) → ℕ) (stepBound : ℕ) :
    (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop where
  | nil (mem : ℕ → ℕ) : BoundedAmortizedTrace phi stepBound mem mem 0 0
  | step {mem₀ mem₁ mem₂ : ℕ → ℕ} {t cStep aStep cRest : ℕ} :
      cStep + phi mem₁ ≤ aStep + phi mem₀ →
      aStep ≤ stepBound →
      BoundedAmortizedTrace phi stepBound mem₁ mem₂ t cRest →
      BoundedAmortizedTrace phi stepBound mem₀ mem₂ (t + 1) (cStep + cRest)

/-- Total cost bound for `t` operations each having amortized cost at most `stepBound`. -/
theorem BoundedAmortizedTrace.bound {phi : (ℕ → ℕ) → ℕ} {stepBound : ℕ}
    {mem₀ memₙ : ℕ → ℕ} {t cTotal : ℕ}
    (ht : BoundedAmortizedTrace phi stepBound mem₀ memₙ t cTotal) :
    cTotal + phi memₙ ≤ t * stepBound + phi mem₀ := by
  induction ht with
  | nil _ => simp
  | @step m₀ m₁ m₂ t' cStep aStep cRest hstep hle _ ih =>
      have h1 : (cStep + cRest) + phi m₂ ≤ stepBound + t' * stepBound + phi m₀ := by omega
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (t' * stepBound) stepBound]
      exact h1

/-- Combining initialization (`O(n)`) with `t` operations bounded by `K * L` and
potential bounded by `K * n * L` yields total cost `≤ initBound + K * t * L`,
or starting mid-stream `≤ K * (t + n) * L`. -/
theorem BoundedAmortizedTrace.init_bound {phi : (ℕ → ℕ) → ℕ} {stepBound : ℕ}
    {mem₀ memₙ : ℕ → ℕ} {cInit cInitBound t cTotal : ℕ}
    (hinit : cInit + phi mem₀ ≤ cInitBound)
    (ht : BoundedAmortizedTrace phi stepBound mem₀ memₙ t cTotal) :
    cInit + cTotal ≤ cInitBound + t * stepBound := by
  have hb := ht.bound
  omega

/-- Starting from any valid representation whose potential is at most `n * stepBound`,
`t` operations each costing at most `stepBound` amortized have total actual cost at most
`(t + n) * stepBound`. -/
theorem BoundedAmortizedTrace.midstream_bound {phi : (ℕ → ℕ) → ℕ} {stepBound n : ℕ}
    {mem₀ memₙ : ℕ → ℕ} {t cTotal : ℕ}
    (hphi : phi mem₀ ≤ n * stepBound)
    (ht : BoundedAmortizedTrace phi stepBound mem₀ memₙ t cTotal) :
    cTotal ≤ (t + n) * stepBound := by
  have hb := ht.bound
  rw [Nat.add_mul]
  omega

/-- Two memories agree on the half-open interval `[a, b)`. -/
def MemAgreeOn (a b : ℕ) (mem₁ mem₂ : ℕ → ℕ) : Prop :=
  ∀ i, a ≤ i → i < b → mem₁ i = mem₂ i

/-- Memory `mem₂` equals `mem₁` everywhere outside `[a, b)`. -/
def MemPreservedOutside (a b : ℕ) (mem₁ mem₂ : ℕ → ℕ) : Prop :=
  ∀ i, i < a ∨ b ≤ i → mem₂ i = mem₁ i

theorem MemPreservedOutside.agree_disjoint {a₁ b₁ a₂ b₂ : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hpres : MemPreservedOutside a₁ b₁ mem₁ mem₂)
    (hdisj : b₂ ≤ a₁ ∨ b₁ ≤ a₂) :
    MemAgreeOn a₂ b₂ mem₁ mem₂ := by
  intro i hi₁ hi₂
  symm
  apply hpres i
  omega

/-- Memory frame for operations that write only inside the node arena `[lo, arenaHi)`,
the bump-heap header word `hdrHeap < lo`, and freshly allocated heap cells
`[mem₁ hdrHeap, mem₂ hdrHeap)`, keeping all earlier memory untouched and maintaining
`ZeroFrom` above the active bump heap pointer. -/
def LctFrame (lo arenaHi hdrHeap : ℕ) (mem₁ mem₂ : ℕ → ℕ) : Prop :=
  hdrHeap < lo ∧
  arenaHi ≤ mem₁ hdrHeap ∧
  mem₁ hdrHeap ≤ mem₂ hdrHeap ∧
  ZeroFrom mem₁ (mem₁ hdrHeap) ∧
  ZeroFrom mem₂ (mem₂ hdrHeap) ∧
  (∀ i, (i < lo ∧ i ≠ hdrHeap) ∨ (arenaHi ≤ i ∧ i < mem₁ hdrHeap) → mem₂ i = mem₁ i)

theorem lctFrame_refl {lo arenaHi hdrHeap : ℕ} {mem : ℕ → ℕ}
    (hhdr : hdrHeap < lo) (hhi : arenaHi ≤ mem hdrHeap) (hz : ZeroFrom mem (mem hdrHeap)) :
    LctFrame lo arenaHi hdrHeap mem mem :=
  ⟨hhdr, hhi, Nat.le_refl _, hz, hz, fun _ _ => rfl⟩

theorem lctFrame_trans {lo arenaHi hdrHeap : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁₂ : LctFrame lo arenaHi hdrHeap m₁ m₂)
    (h₂₃ : LctFrame lo arenaHi hdrHeap m₂ m₃) :
    LctFrame lo arenaHi hdrHeap m₁ m₃ := by
  rcases h₁₂ with ⟨hhdr, hhi₁, hle₁₂, hz₁, _, hag₁₂⟩
  rcases h₂₃ with ⟨_, _, hle₂₃, _, hz₃, hag₂₃⟩
  refine ⟨hhdr, hhi₁, le_trans hle₁₂ hle₂₃, hz₁, hz₃, ?_⟩
  intro i hi
  rcases hi with ⟨hlo, hne⟩ | ⟨hge, hlt⟩
  · exact (hag₂₃ i (Or.inl ⟨hlo, hne⟩)).trans (hag₁₂ i (Or.inl ⟨hlo, hne⟩))
  · exact (hag₂₃ i (Or.inr ⟨hge, lt_of_lt_of_le hlt hle₁₂⟩)).trans (hag₁₂ i (Or.inr ⟨hge, hlt⟩))

theorem lctFrame_of_memPreservedOutside {lo arenaHi hdrHeap : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hpres : MemPreservedOutside lo arenaHi m₁ m₂)
    (hhdr : hdrHeap < lo) (hhi : arenaHi ≤ m₁ hdrHeap) (hz₁ : ZeroFrom m₁ (m₁ hdrHeap)) :
    LctFrame lo arenaHi hdrHeap m₁ m₂ := by
  have heq_hdr : m₂ hdrHeap = m₁ hdrHeap := hpres hdrHeap (Or.inl hhdr)
  refine ⟨hhdr, hhi, by rw [heq_hdr], hz₁, ?_, ?_⟩
  · intro i hi
    rw [heq_hdr] at hi
    rw [hpres i (Or.inr (le_trans hhi hi))]
    exact hz₁ i hi
  · intro i hi
    rcases hi with ⟨hlo, _⟩ | ⟨hge, _⟩
    · exact hpres i (Or.inl hlo)
    · exact hpres i (Or.inr hge)

theorem lctFrame_update_arena {lo arenaHi hdrHeap addr val : ℕ} {mem : ℕ → ℕ}
    (hlo : lo ≤ addr) (hhi : addr < arenaHi)
    (hhdr : hdrHeap < lo) (hheap : arenaHi ≤ mem hdrHeap) (hz : ZeroFrom mem (mem hdrHeap)) :
    LctFrame lo arenaHi hdrHeap mem (Function.update mem addr val) := by
  refine lctFrame_of_memPreservedOutside ?_ hhdr hheap hz
  intro i hi
  have hne : i ≠ addr := by rcases hi with h | h <;> omega
  exact Function.update_of_ne hne val mem

theorem lctFrame_of_heapStep {lo arenaHi hdrHeap hp' : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hhdr : hdrHeap < lo) (hlohi : lo ≤ arenaHi) (harena : arenaHi ≤ m₁ hdrHeap)
    (hle : m₁ hdrHeap ≤ hp')
    (hz₁ : ZeroFrom m₁ (m₁ hdrHeap)) (hz₂ : ZeroFrom m₂ hp')
    (hpres_lt : ∀ i < m₁ hdrHeap, i ≠ hdrHeap → m₂ i = m₁ i)
    (hhdr_eq : m₂ hdrHeap = hp') :
    LctFrame lo arenaHi hdrHeap m₁ m₂ := by
  refine ⟨hhdr, harena, by omega, hz₁, by simpa [hhdr_eq] using hz₂, ?_⟩
  intro i hi
  rcases hi with ⟨hlo, hne⟩ | ⟨hge, hlt⟩
  · exact hpres_lt i (by omega) hne
  · exact hpres_lt i hlt (by omega)

end

end MinCostFlow.LinkCut.Prog
