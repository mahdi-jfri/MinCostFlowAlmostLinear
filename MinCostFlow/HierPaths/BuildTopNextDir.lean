module

public import MinCostFlow.HierPaths.BuildTopNext

/-!
# Filling the graph directory for the next depth

Read each child graph address and save it in group order. The reply
blocks are below the new directory and remain in place.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The arguments are the reply directory, new graph directory, branching, and child count. -/
def buildTopNextDir (row : ℕ) : Stmt :=
  forRange 4 (.const 0) (.reg 3)
    (.call 5 row [.reg 0, .reg 4, .reg 2, .reg 1]) ;;
  .ret (.const 0)

theorem buildTopNextDir_noRand (row : ℕ) : (buildTopNextDir row).NoRand := by
  simp [buildTopNextDir, forRange, forUp, Stmt.NoRand]

def buildTopNextDirContract (w parents k : ℕ) (addr : ℕ → ℕ) (reply : ℕ → BuildLevelData) :
    Contract where
  pre args mem := ∃ dir dst, args = [dir, dst, k, parents * k] ∧ 0 < k ∧
    dir + parents ≤ dst ∧ dst + parents * k < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ g < parents, mem (dir + g) = addr g ∧
      addr g + ((reply g).encode k).length ≤ dst ∧ ListAt mem (addr g) ((reply g).encode k)
  post args mem _ mem' := ∃ dir dst, args = [dir, dst, k, parents * k] ∧
    (∀ i < parents * k, mem' (dst + i) = buildTopChildAddr (addr (i / k)) k
        (i % k) (reply (i / k))) ∧
    ∀ x, x < dst ∨ dst + parents * k ≤ x → mem' x = mem x
  cost _ _ := 100 * (parents * k) + 15

theorem buildTopNextDir_meetsContract {w f row read seek parents k : ℕ} {p : Program}
    {addr : ℕ → ℕ} {reply : ℕ → BuildLevelData}
    (hp : p.procs[f]? = some (buildTopNextDir row))
    (hr : p.procs[row]? = some (buildTopNextRow read))
    (ha : p.procs[read]? = some (buildTopReplyRead seek))
    (hs : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f (buildTopNextDirContract w parents k addr reply) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨dir, dst, rfl, hk, hsep, hroom, h1, hrows⟩ := hpre
  let n := parents * k
  let loc := fun i => buildTopChildAddr (addr (i / k)) k (i % k) (reply (i / k))
  let I := fun i (s : State) =>
    s.regs 0 = dir ∧ s.regs 1 = dst ∧ s.regs 2 = k ∧ s.regs 3 = n ∧ s.regs 4 = i ∧
    (∀ j < i, s.mem (dst + j) = loc j) ∧
    ∀ x, x < dst ∨ dst + i ≤ x → s.mem x = mem x
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 4) (lo := .const 0) (hi := .reg 3)
    (body := .call 5 row [.reg 0, .reg 4, .reg 2, .reg 1])
    (P := fun t => t = startState [dir, dst, k, n] mem pos) (Inv := I)
    90 0 n (Nat.zero_le _) h1 (fun _ => by omega)
    (fun t ht => by subst t; exact ⟨Expr.eval_const (Nat.two_pow_pos _),
      rfl, rfl, rfl, rfl, by simp, fun j hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.1) ?_
  · refine runs_start_le ?_
    unfold buildTopNextDir
    refine runs_seq_triple_le hloop rfl ?_
    intro t ⟨_, _, _, _, _, htbl, hf⟩
    refine runs_ret_le (Expr.eval_const (Nat.two_pow_pos w)) ⟨dir, dst, rfl, htbl, hf⟩ ?_
    simp [buildTopNextDirContract, Expr.size, n]
    omega
  intro i _ hi s ω' ⟨r0,r1,r2,r3,r4,hTbl,hFrame⟩
  have hg : i / k < parents := (Nat.div_lt_iff_lt_mul hk).mpr hi
  obtain ⟨hAddr, hBlock, hData⟩ := hrows (i / k) hg
  have hsrc : dir + i / k < dst := by omega
  have hd : dst + i < 2 ^ w := by omega
  have hdata : ListAt s.mem (addr (i/k)) ((reply (i/k)).encode k) :=
    listAt_congr (fun j hj => (hFrame _ (.inl (by omega))).symm) hData
  refine runs_start_le ?_
  refine runs_call_le (buildTopNextRow_meetsContract (w := w) (i := i)
    (k := k) (a := addr (i/k)) (D := reply (i/k)) hr ha hs) (vs := [dir,i,k,dst])
    ?_ ?_ ⟨dir,dst,rfl,hk,by omega,hd,(hFrame _ (.inl hsrc)).trans hAddr,hdata,by omega⟩ ?_
  · simp [evalArgs, Expr.eval, r0,r1,r2,r4]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · omega
    · exact hw _ (by simp)
    · exact hw _ (by simp)
  · intro v mem' pos' hpost
    obtain ⟨dir',dst',he,hv,hmem⟩ := hpost
    simp only [List.cons.injEq, and_true, true_and] at he
    obtain ⟨_,_⟩ := he
    subst dir' dst' mem' v
    refine ⟨⟨⟨?_, ?_, ?_, ?_, by simp, ?_, ?_⟩, ?_⟩, ?_⟩
    · simpa using r0
    · simpa using r1
    · simpa using r2
    · simpa using r3
    · intro j hj
      by_cases he : j = i
      · subst j
        exact Function.update_self ..
      · exact (Function.update_of_ne (by omega) _ _).trans (hTbl j (by omega))
    · intro x hx
      exact (Function.update_of_ne (by rcases hx with ha | ha <;> omega) _ _).trans
        (hFrame _ (hx.imp_right (by omega)))
    · simpa using r4
    · simp [buildTopNextRowContract, Expr.size, argsSize]

end MinCostFlow.HierPaths

end
