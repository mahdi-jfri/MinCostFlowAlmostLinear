module

public import WordRAM.DataStructure
import WordRAM.Exec

/-!
# Relocating procedure indices in Word RAM programs

A self-contained `WordRAM.Program` `Q` can be embedded at an arbitrary offset
`offset` inside a host program `p` by adding `offset` to every procedure index
in `.call` statements. This preserves determinism, execution outcomes, states,
and exact step counts, so any `MeetsContract` or `DSRep.Implements` proof for
`Q` transfers directly to `p`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Shift every callee procedure index in a statement by `offset`. -/
@[expose] def shiftProcIds (offset : ℕ) : Stmt → Stmt
  | .nop => .nop
  | .assign r e => .assign r e
  | .store a v => .store a v
  | .rand r => .rand r
  | .seq s t => .seq (shiftProcIds offset s) (shiftProcIds offset t)
  | .cond e s t => .cond e (shiftProcIds offset s) (shiftProcIds offset t)
  | .loop e body => .loop e (shiftProcIds offset body)
  | .call r f args => .call r (offset + f) args
  | .ret e => .ret e

/-- Shifted procedure list of a standalone program `Q`. -/
@[expose] def shiftProgramProcs (offset : ℕ) (Q : Program) : List Stmt :=
  Q.procs.map (shiftProcIds offset)

theorem shiftProcIds_noRand (offset : ℕ) (s : Stmt) :
    (shiftProcIds offset s).NoRand ↔ s.NoRand := by
  induction s with
  | seq s t ihs iht => simp [shiftProcIds, Stmt.NoRand, ihs, iht]
  | cond e s t ihs iht => simp [shiftProcIds, Stmt.NoRand, ihs, iht]
  | loop e body ih => simp [shiftProcIds, Stmt.NoRand, ih]
  | _ => simp [shiftProcIds, Stmt.NoRand]

theorem shiftProgramProcs_noRand {offset : ℕ} {Q : Program} (hdet : Q.IsDeterministic) :
    ∀ s ∈ shiftProgramProcs offset Q, s.NoRand := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (shiftProcIds_noRand offset t).mpr (hdet t ht)

private theorem exec_shiftProcIds {w offset : ℕ} {Q p : Program} {ω : ℕ → Bool}
    (hp : p.HasAt offset (shiftProgramProcs offset Q)) :
    ∀ (fuel : ℕ) (s : Stmt) (st : State) (res : Outcome × State × ℕ),
      exec w Q ω fuel s st = some res →
      exec w p ω fuel (shiftProcIds offset s) st = some res := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [exec] at h
  | succ fuel ih =>
    intro s st res h
    cases s with
    | nop => simpa [shiftProcIds, exec] using h
    | assign r e => simpa [shiftProcIds, exec] using h
    | store a v => simpa [shiftProcIds, exec] using h
    | rand r => simpa [shiftProcIds, exec] using h
    | ret e => simpa [shiftProcIds, exec] using h
    | seq s t =>
      simp only [shiftProcIds, exec] at h ⊢
      cases hs : exec w Q ω fuel s st with
      | none => simp [hs] at h
      | some v =>
        rcases v with ⟨o, st', c⟩
        rw [ih s st _ hs]
        cases o with
        | returned u => simpa [hs] using h
        | normal =>
          simp only [hs] at h
          dsimp only
          cases ht : exec w Q ω fuel t st' with
          | none => rw [ht] at h; cases h
          | some v' =>
            rw [ih t st' _ ht]
            rw [ht] at h
            exact h
    | cond e s t =>
      simp only [shiftProcIds, exec] at h ⊢
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h ⊢
        by_cases hv : v = 0
        · simp only [hv, ↓reduceIte] at h ⊢
          cases ht : exec w Q ω fuel t st with
          | none => rw [ht] at h; cases h
          | some vt => rw [ih t st _ ht]; rw [ht] at h; exact h
        · simp only [hv, ↓reduceIte] at h ⊢
          cases hs : exec w Q ω fuel s st with
          | none => rw [hs] at h; cases h
          | some vs => rw [ih s st _ hs]; rw [hs] at h; exact h
    | loop e body =>
      simp only [shiftProcIds, exec] at h ⊢
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h ⊢
        by_cases hv : v = 0
        · simpa [hv] using h
        · simp only [hv, ↓reduceIte] at h ⊢
          cases hb : exec w Q ω fuel body st with
          | none => simp [hb] at h
          | some vb =>
            rcases vb with ⟨o, st', c⟩
            rw [ih body st _ hb]
            cases o with
            | returned u => simpa [hb] using h
            | normal =>
              simp only [hb] at h
              cases hl : exec w Q ω fuel (.loop e body) st' with
              | none => simp [hl] at h
              | some vl =>
                have hl' := ih (.loop e body) st' _ hl
                change (match exec w p ω fuel (shiftProcIds offset (.loop e body)) st' with
                  | none => none | some (o, st'', c') => some (o, st'', e.size + c + c' + 1)) = some res
                rw [hl']
                rw [hl] at h
                exact h
    | call r f args =>
      simp only [shiftProcIds, exec] at h ⊢
      cases ha : evalArgs w st args with
      | none => simp [ha] at h
      | some vs =>
        simp only [ha] at h ⊢
        cases hf : Q.procs[f]? with
        | none => simp [hf] at h
        | some body =>
          have hfl : f < Q.procs.length := by
            by_contra hge
            simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hf
          have hbody : Q.procs[f] = body := by
            rw [List.getElem?_eq_getElem hfl] at hf
            exact Option.some.inj hf
          have hpf : p.procs[offset + f]? = some (shiftProcIds offset body) := by
            have hmem := hp f (by simp [shiftProgramProcs, hfl])
            simpa [shiftProgramProcs, hbody] using hmem
          simp only [hf] at h
          simp only [hpf]
          change (match exec w Q ω fuel body { st with regs := fun i => vs.getD i 0 } with
            | none => none | some (o, st', c) => _) = some res at h
          cases hb : exec w Q ω fuel body { st with regs := fun i => vs.getD i 0 } with
          | none => rw [hb] at h; cases h
          | some vb =>
            rw [ih body _ _ hb]
            rw [hb] at h
            exact h

/-- Executing a shifted statement in a host program that embeds `Q` at `offset`
matches every run of `Q`. -/
theorem runs_shiftProcIds {w offset : ℕ} {Q p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (hr : Runs w Q ω s st o st' c) :
    Runs w p ω (shiftProcIds offset s) st o st' c := by
  obtain ⟨fuel, hfuel⟩ := hr
  exact ⟨fuel, exec_shiftProcIds hp fuel s st (o, st', c) hfuel⟩

/-- A `MeetsContract` proof for a standalone program `Q` transfers to any host
program `p` embedding `shiftProgramProcs offset Q` at `offset`. -/
theorem meetsContract_shift {w offset entry : ℕ} {Q p : Program} {C : Contract}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (hm : MeetsContract w Q entry C) :
    MeetsContract w p (offset + entry) C := by
  intro args mem pos ω hwords hpre
  obtain ⟨body, hbody, o, st', c, hr, hpost, hc⟩ := hm args mem pos ω hwords hpre
  have hlen : entry < Q.procs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
  have hbe : Q.procs[entry] = body := by
    rw [List.getElem?_eq_getElem hlen] at hbody
    exact Option.some.inj hbody
  have hpentry : p.procs[offset + entry]? = some (shiftProcIds offset body) := by
    have hmem := hp entry (by simp [shiftProgramProcs, hlen])
    simpa [shiftProgramProcs, hbe] using hmem
  exact ⟨shiftProcIds offset body, hpentry, o, st', c, runs_shiftProcIds hp hr, hpost, hc⟩

/-- A `DSRep.Implements` proof for a standalone program `Q` transfers to any
host program `p` embedding `shiftProgramProcs offset Q` at `offset`. -/
theorem dsRep_implements_shift {S : Type} {R : DSRep S} {w offset init : ℕ}
    {op : ℕ → ℕ} {Q p : Program} {D : DataStructure S}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (himpl : R.Implements w Q init op D) :
    R.Implements w p (offset + init) (fun i => offset + op i) D := by
  refine ⟨himpl.1, ?_, ?_⟩
  · intro args mem pos ω hwords hpre hz hroom
    obtain ⟨body, hbody, o, st', c, hr, s, x, hrep, hpost, hresp, hc⟩ :=
      himpl.2.1 args mem pos ω hwords hpre hz hroom
    have hlen : init < Q.procs.length := by
      by_contra hge
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
    have hbe : Q.procs[init] = body := by
      rw [List.getElem?_eq_getElem hlen] at hbody
      exact Option.some.inj hbody
    have hpinit : p.procs[offset + init]? = some (shiftProcIds offset body) := by
      have hmem := hp init (by simp [shiftProgramProcs, hlen])
      simpa [shiftProgramProcs, hbe] using hmem
    exact ⟨shiftProcIds offset body, hpinit, o, st', c, runs_shiftProcIds hp hr,
      s, x, hrep, hpost, hresp, hc⟩
  · intro i b s x args mem pos ω hwords hb hrep hpre hfoot hz hroom
    obtain ⟨body, hbody, o, st', c, hr, s', y, hrep', hpost, hresp, hc⟩ :=
      himpl.2.2 i b s x args mem pos ω hwords hb hrep hpre hfoot hz hroom
    have hlen : op i < Q.procs.length := by
      by_contra hge
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
    have hbe : Q.procs[op i] = body := by
      rw [List.getElem?_eq_getElem hlen] at hbody
      exact Option.some.inj hbody
    have hpop : p.procs[offset + op i]? = some (shiftProcIds offset body) := by
      have hmem := hp (op i) (by simp [shiftProgramProcs, hlen])
      simpa [shiftProgramProcs, hbe] using hmem
    exact ⟨shiftProcIds offset body, hpop, o, st', c, runs_shiftProcIds hp hr,
      s', y, hrep', hpost, hresp, hc⟩

end MinCostFlow.MinRatio
