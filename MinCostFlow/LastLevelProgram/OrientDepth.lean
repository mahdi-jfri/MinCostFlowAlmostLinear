module

public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Ordering endpoints for the ancestor query

Compare the two stored depths, put the deeper endpoint first, and
subtract the smaller depth from the larger depth.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Orient the endpoints in registers three and four using their
depths in registers eleven and twelve. -/
def orientDepth : Stmt :=
  .cond (.bin .lt (.reg 11) (.reg 12))
    (.assign 9 (.reg 3) ;;
      .assign 3 (.reg 4) ;;
      .assign 4 (.bin .sub (.reg 12) (.reg 11)))
    (.assign 9 (.reg 4) ;;
      .assign 4 (.bin .sub (.reg 11) (.reg 12)))

/-- The oriented first endpoint is at least as deep as the second.
The output is in the argument registers of `ancestorQuery`. -/
theorem orientDepth_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v du dv : ℕ) (hw : 1 < 2^w)
    (hdu : du < 2^w) (hdv : dv < 2^w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧
        st.regs 11 = du ∧ st.regs 12 = dv)
      orientDepth (normalPost fun st => st.mem = mem ∧ st.regs 0 = base ∧
        st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = (if du < dv then v else u) ∧
        st.regs 9 = (if du < dv then u else v) ∧
        st.regs 4 = (if du < dv then dv-du else du-dv))
      (fun _ => 14) := by
  intro st ω ⟨hm,h0,h1,h2,h3,h4,h11,h12⟩
  have hab : du-dv < 2^w := (Nat.sub_le ..).trans_lt hdu
  have hba : dv-du < 2^w := (Nat.sub_le ..).trans_lt hdv
  unfold orientDepth
  have he : (Expr.bin .lt (.reg 11) (.reg 12)).eval w st =
      some (if du < dv then 1 else 0) := by eval_expr
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  refine runs_cond_le (k := 0) he ?_ ?_
  · intro hn
    have h : du < dv := by by_contra h; exact hn (ite_eq_right h)
    simp only [ite_eq_left h]
    wram_run
    all_goals simp [normalPost, Expr.size, hm,h0,h1,h2,h4,h11,h12]
  · intro hz
    have h : ¬ du < dv := by intro h; simp [h] at hz
    simp only [ite_eq_right h]
    wram_run
    all_goals simp [normalPost, Expr.size, hm,h0,h1,h2,h3,h11,h12]

/-- Read the two depths from a one-word-per-vertex array based at register ten. -/
def readEndpointDepths : Stmt :=
  .assign 11 (.load (.bin .add (.reg 10) (.reg 3))) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.reg 4)))

/-- Two array reads give the depths and leave the vertices and ancestor table
arguments in place. -/
theorem readEndpointDepths_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v depthBase : ℕ) (depth : ℕ → ℕ)
    (hu : u < n) (hv : v < n) (hroom : depthBase+n < 2^w)
    (hdepth : ∀ x < n, mem (depthBase+x) = depth x) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧ st.regs 10 = depthBase)
      readEndpointDepths
      (normalPost fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧
        st.regs 11 = depth u ∧ st.regs 12 = depth v) (fun _ => 11) := by
  intro st ω hP
  conv => congr; ext o; congr; ext st'; congr; ext c; arg 2; arg 2; arg 1; rw [← Nat.zero_add c]
  obtain ⟨hm,h0,h1,h2,h3,h4,h10⟩ := hP
  have haddrU : depthBase+u < 2^w := by omega
  have haddrV : depthBase+v < 2^w := by omega
  have hreadU : st.mem (depthBase+u) = depth u := hm ▸ hdepth u hu
  have hreadV : st.mem (depthBase+v) = depth v := hm ▸ hdepth v hv
  unfold readEndpointDepths
  wram_run
  all_goals simp [normalPost, Expr.size, hm,h0,h1,h2,h3,h4,h10,hreadU,hreadV]

/-- Read depths and orient the endpoints for the ancestor query. -/
def prepareAncestorQuery : Stmt :=
  readEndpointDepths ;; orientDepth

/-- Preparing the endpoint arguments costs at most 26 steps. -/
theorem prepareAncestorQuery_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v depthBase : ℕ) (depth : ℕ → ℕ)
    (hw : 1 < 2^w) (hu : u < n) (hv : v < n) (hroom : depthBase+n < 2^w)
    (hdepth : ∀ x < n, mem (depthBase+x) = depth x)
    (hdu : depth u < 2^w) (hdv : depth v < 2^w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧ st.regs 10 = depthBase)
      prepareAncestorQuery (normalPost fun st => st.mem = mem ∧ st.regs 0 = base ∧
        st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = (if depth u < depth v then v else u) ∧
        st.regs 9 = (if depth u < depth v then u else v) ∧
        st.regs 4 = (if depth u < depth v then depth v-depth u else depth u-depth v))
      (fun _ => 26) :=
  Triple.seq_normal_const
    (readEndpointDepths_triple mem base n count u v depthBase depth hu hv hroom hdepth)
    (orientDepth_triple mem base n count u v (depth u) (depth v) hw hdu hdv)

end MinCostFlow.LastLevelProgram
