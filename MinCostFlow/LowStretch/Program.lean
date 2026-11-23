module

public import MinCostFlow.LowStretch.ProgRec
public import MinCostFlow.LowStretch.ProgRecFit

/-!
# The whole program

`lsstProg body` is the program of the low-stretch spanning tree, as one list of procedures:
* `0`: the entry `entryB 27`;
* `1` to `26`: the preprocessing `preProcs 1` (with `copyWords` at `26`);
* `27`: the root procedure `rootP 29 28`;
* `28`: `mxP`, the largest rounded weight;
* `29`: the cluster procedure `recP 30 29 26`;
* `30` on: the procedures of the body, `body 30`. The body itself is the first of them.

`lowStretchSpanningTree_of_prog` gives `LowStretchSpanningTree` from the contract of the body at
`A = bodyA`, by `lowStretchSpanningTree_of_body`. The facts `HasAt` it asks for come from
`hasAt_mid`: a list in the middle of the procedures is at the index of its start.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- **The program**, with the procedures `body 30` of the body from index `30` on. -/
def lsstProg (body : ℕ → List Stmt) : Program :=
  ⟨(entryB 27 :: preProcs 1) ++ [rootP 29 28, mxP, recP 30 29 26] ++ body 30⟩

/-- A list in the middle of the procedures is at the index of its start. -/
theorem hasAt_mid {l₁ l₂ l₃ : List Stmt} {b : ℕ} (hb : b = l₁.length) :
    (Program.mk (l₁ ++ l₂ ++ l₃)).HasAt b l₂ := by
  subst hb
  intro i hi
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem lsstProg_entry (body : ℕ → List Stmt) :
    (lsstProg body).HasAt 0 (entryB 27 :: preProcs 1) := by
  have := hasAt_mid (l₁ := []) (l₂ := entryB 27 :: preProcs 1)
    (l₃ := [rootP 29 28, mxP, recP 30 29 26] ++ body 30) rfl
  simpa [lsstProg, List.append_assoc, preProcs_length] using this

theorem lsstProg_root (body : ℕ → List Stmt) : (lsstProg body).HasAt 27 [rootP 29 28] := by
  have := hasAt_mid (l₁ := entryB 27 :: preProcs 1) (l₂ := [rootP 29 28])
    (l₃ := [mxP, recP 30 29 26] ++ body 30) rfl
  simpa [lsstProg, List.append_assoc, preProcs_length] using this

theorem lsstProg_mx (body : ℕ → List Stmt) : (lsstProg body).HasAt 28 [mxP] := by
  have := hasAt_mid (l₁ := (entryB 27 :: preProcs 1) ++ [rootP 29 28]) (l₂ := [mxP])
    (l₃ := [recP 30 29 26] ++ body 30) rfl
  simpa [lsstProg, List.append_assoc, preProcs_length] using this

theorem lsstProg_rec (body : ℕ → List Stmt) : (lsstProg body).HasAt 29 [recP 30 29 26] := by
  have := hasAt_mid (l₁ := (entryB 27 :: preProcs 1) ++ [rootP 29 28, mxP])
    (l₂ := [recP 30 29 26]) (l₃ := body 30) rfl
  simpa [lsstProg, List.append_assoc, preProcs_length] using this

theorem lsstProg_body (body : ℕ → List Stmt) : (lsstProg body).HasAt 30 (body 30) := by
  have := hasAt_mid (l₁ := (entryB 27 :: preProcs 1) ++ [rootP 29 28, mxP, recP 30 29 26])
    (l₂ := body 30) (l₃ := []) rfl
  simpa [lsstProg, preProcs_length] using this

/-- **[AN19] Theorem 1** from the contract of the body. The procedure `30` of `lsstProg body`
(the first of `body 30`) must meet `MeetsBody` at `A = bodyA`, at every word size. -/
theorem lowStretchSpanningTree_of_prog (body : ℕ → List Stmt)
    (h : ∀ w, MeetsBody w bodyA (lsstProg body) 30) : LowStretchSpanningTree :=
  lowStretchSpanningTree_of_body ⟨lsstProg body, bodyA, 27, 29, 28, 30, lsstProg_entry body,
    lsstProg_root body, lsstProg_mx body, lsstProg_rec body, by unfold recK bodyA; omega, h⟩

end MinCostFlow.LowStretch
