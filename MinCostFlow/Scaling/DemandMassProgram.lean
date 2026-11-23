module

public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.DemandReduction
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Computing the feasibility phase's artificial capacity

The feasibility test in Lemma C.1 of Chen et al., arXiv:2203.00671v2,
Appendix C, compares its objective with minus the total artificial
capacity. At a vertex the two artificial capacities are the positive and
negative parts of the shifted demand. Their sum is its absolute value.
A scan of the canonical demand pairs therefore sums their magnitude words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[signedDemands,count]`. -/
def demandMassBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .call 3 self [.bin .add (.reg 0) (.const 2),.bin .sub (.reg 1) (.const 1)] ;;
     .ret (.bin .add (.reg 2) (.reg 3)))

/-- A single recursive procedure sums the magnitudes. -/
def demandMassModule (b : ℕ) : List Stmt := [demandMassBody b]

/-- All sums fit the supplied width, and the source stays unchanged. -/
def demandMassContract (w : ℕ) (zs : List ℤ) : Contract where
  pre args mem := ∃ src,args=[src,zs.length] ∧ ListAt mem src (zs.flatMap encodeInt) ∧
    src+2*zs.length<2^w ∧ (zs.map Int.natAbs).sum<2^w ∧ 2<2^w
  post _ mem ret mem' := mem'=mem ∧ ret=(zs.map Int.natAbs).sum
  cost _ _ := 40*zs.length+20

/-- The mass scan has no random instruction. -/
theorem demandMassModule_noRand (b : ℕ) : ∀ body∈demandMassModule b,body.NoRand := by
  intro body hb
  have he : body=demandMassBody b := by simpa only [demandMassModule,List.mem_singleton] using hb
  subst body
  simp only [demandMassBody,Stmt.NoRand,and_self]

/-- Summing the magnitude words computes the exact total artificial
capacity, with unchanged memory and explicit linear cost. -/
theorem demandMass_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (demandMassModule b)) (zs : List ℤ) :
    MeetsContract w p b (demandMassContract w zs) := by
  induction zs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨src,rfl,_,_,_,h2⟩ := hpre
    apply runs_start_le
    unfold demandMassBody
    wram_step
    · refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,rfl⟩ ?_
      simp only [demandMassContract,List.length_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
      omega
    · simp at hcond
  | cons z zs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨src,rfl,hat,hend,hsum,h2⟩ := hpre
    obtain ⟨hpair,htail⟩ := listAt_append.mp hat
    change ListAt mem src (encodeInt z) at hpair
    change ListAt mem (src+2) (zs.flatMap encodeInt) at htail
    have hmag : mem (src+1)=z.natAbs := hpair 1 (by change 1<2; omega)
    have hsrc1 : src+1<2^w := by simp only [List.length_cons] at hend; omega
    have hsrc2 : src+2<2^w := by simp only [List.length_cons] at hend; omega
    have hsum' : z.natAbs+(zs.map Int.natAbs).sum<2^w := hsum
    have hmagWord : z.natAbs<2^w := by omega
    have htailWord : (zs.map Int.natAbs).sum<2^w := by omega
    have hlenWord : zs.length<2^w := by simp only [List.length_cons] at hend; omega
    apply runs_start_le
    unfold demandMassBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := z.natAbs) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [src+2,zs.length]) ?_ (by wram_words) ?_ ?_
      · have he : (z::zs).length-1=zs.length := rfl
        rw [←he]; eval_expr
      · refine ⟨src+2,rfl,htail,?_,htailWord,h2⟩
        simp only [List.length_cons] at hend
        omega
      · intro mass memR posR hpostR
        obtain ⟨hmem,hmass⟩ := hpostR
        change memR=mem at hmem
        change mass=(zs.map Int.natAbs).sum at hmass
        have hresult : z.natAbs+mass<2^w := by omega
        refine runs_ret_le (v := z.natAbs+mass) (by eval_expr) ?_ ?_
        · exact ⟨hmem,by change z.natAbs+mass=z.natAbs+(zs.map Int.natAbs).sum; rw [hmass]⟩
        · simp only [demandMassContract,List.length_cons,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

/-- Every signed demand list realizes all mass-scan entry conditions
jointly in its canonical source memory at some finite width. -/
theorem exists_demandMass_pre (zs : List ℤ) :
    ∃ w,(∀ x∈[0,zs.length],x<2^w) ∧
      (demandMassContract w zs).pre [0,zs.length] (initMem (zs.flatMap encodeInt)) := by
  let w := (zs.map Int.natAbs).sum+2*zs.length+3
  have hw : (zs.map Int.natAbs).sum+2*zs.length+3<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,0,rfl,listAt_initMem _,by omega,by omega,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

/-- The absolute-demand sum is exactly the mass in the paper's auxiliary
circulation definition, since the positive and negative parts sum to the
absolute value at each vertex. -/
theorem demandMass_eq_magnitude_sum (J : Circulation) (d : Fin J.n → ℤ) :
    J.demandMass d=((List.ofFn d).map Int.natAbs).sum := by
  unfold Circulation.demandMass
  rw [List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  change (d v).toNat+(-(d v)).toNat=(d v).natAbs
  omega

end MinCostFlow.Scaling.Machine
