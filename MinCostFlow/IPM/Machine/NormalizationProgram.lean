module

public import MinCostFlow.IPM.Machine.DyadicBlock
public import MinCostFlow.IPM.Machine.PrecisionParameters
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A representable requested step normalization

For dyadic quality `kappa=2^-k` and stored barrier exponent `a=2^-j`,
the paper's requested normalization is `(kappa*a/32)^2/50`.
Using denominator 64 in place of 50 makes the normalization dyadic.
Its ratio to the source normalization is exactly `25/32`, within the
initial storage-rounding interval. This is the allowed scalar rounding
in the adapted Lemma 9.3, not rounding individual flow coordinates.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Binary exponent for the exactly represented normalization. -/
def dyadicNormalizationExponent (k j : ℕ) : ℕ := 2*(k+j)+16

/-- The dyadic request is exactly `25/32` times the source normalization. -/
theorem dyadicNormalization_eq (k j : ℕ) :
    1/(2:ℝ)^(dyadicNormalizationExponent k j) =
      (25/32:ℝ)*(((1/(2:ℝ)^k)*(1/(2:ℝ)^j)/32)^2/50) := by
  rw [show dyadicNormalizationExponent k j=(k+j)*2+16 by
    unfold dyadicNormalizationExponent; omega,pow_add,pow_mul,pow_add]
  norm_num
  field_simp
  ring

/-- Arguments `[kappaExponent,alphaExponent,L,P,heap]`. -/
def normalizationBody (store : ℕ) : Stmt :=
  .assign 5 (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 0) (.reg 1))) (.const 16)) ;;
  .call 6 store [.reg 5,.reg 2,.reg 3,.reg 4] ;;
  .ret (.reg 6)

/-- Exponent arithmetic followed by exact single-bit storage. -/
def normalizationModule (_b : ℕ) : List Stmt :=
  [normalizationBody (_b+1)] ++ dyadicBlockModule

/-- The normalization is stored exactly, with its entire block framed. -/
def normalizationContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ k j L P heap,args=[k,j,L,P,heap] ∧
      dyadicNormalizationExponent k j ≤ P ∧ P+2 ≤ 4*L)
    (fun args _ mem' => ScalarAt mem' (heapArg args) 4 (args.getD 2 0) (args.getD 3 0)
      (1/(2:ℝ)^(dyadicNormalizationExponent (args.getD 0 0) (args.getD 1 0))))
    (fun _ _ => 150) (fun args _ => args.getD 2 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+args.getD 2 0}

/-- The normalization entry contains no random instruction. -/
theorem normalizationModule_noRand (b : ℕ) :
    ∀ body ∈ normalizationModule b,body.NoRand := by
  intro body hb
  simp only [normalizationModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [normalizationBody,Stmt.NoRand]
  · have he : body=dyadicBlockBody := by simpa [dyadicBlockModule] using hb
    subst body
    exact dyadicBlock_noRand

/-- The requested normalization is computed and stored in at most 150
operations. Only its common scalar is rounded relative to the source. -/
theorem normalization_meetsContract {w b : ℕ} {p : Program} (hw : 16 < 2^w)
    (hp : p.HasAt b (normalizationModule b)) :
    MeetsContract w p b (normalizationContract w) := by
  have hstore : p.HasAt (b+1) dyadicBlockModule := Num.hasAt_append_right hp
  have hstoreSpec := dyadicBlock_meetsContract hw hstore
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨k,j,L,P,heap,rfl,hk,hwidth⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+L < 2^w at hspace
  have hkw : k < 2^w := hwords _ (by simp)
  have hjw : j < 2^w := hwords _ (by simp)
  have hLw : L < 2^w := hwords _ (by simp)
  have hPw : P < 2^w := hwords _ (by simp)
  have hhw : heap < 2^w := hwords _ (by simp)
  have hcalc : 2*(k+j)+16 < 2^w := hk.trans_lt hPw
  apply runs_start_le
  unfold normalizationBody
  wram_step
  refine runs_seq_call_le hstoreSpec
    (vs:=[dyadicNormalizationExponent k j,L,P,heap]) (by unfold dyadicNormalizationExponent; eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_,L,P,heap,rfl,hk,hwidth⟩,hzero,hspace⟩
  · intro v mem1 pos1 hp1
    obtain ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩ := hp1
    change v=heap+L at hv
    have hvw : v < 2^w := hv ▸ hspace
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · exact ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩
    · simp [normalizationContract,dyadicBlockContract,heapContract,argsSize,startState,
        Expr.size_bin,Expr.size_const,Expr.size_reg]

/-- The stored barrier exponent is covered by the slack range exponent. -/
theorem alphaExponent_le_slackRange (m U : ℕ) (hsize : 2 ≤ m*U) :
    Num.IPM.alphaExponent m U ≤ slackRangeExponent m U := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by intro he; simp [he] at hsize)
  have hb : 1 ≤ m.size+U.size := by have hh := Nat.size_pos.mpr hm; omega
  have hsq : m.size+U.size ≤ (m.size+U.size)^2 := by nlinarith only [hb]
  have hscale : Num.IPM.alphaScale m U ≤ slackRangeExponent m U := by
    unfold Num.IPM.alphaScale slackRangeExponent
    omega
  exact ((Num.IPM.alphaExponent_le_iff m U _).mpr Nat.lt_two_pow_self.le).trans hscale

/-- The actual normalization program stores precisely the request used
by the dyadic-step model when quality is `2^-k` and alpha is the numerical
interface's stored exponent. -/
theorem normalization_output_for_dyadic_quality (m U k : ℕ)
    {w L P heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (normalizationContract w).post [k,Num.IPM.alphaExponent m U,L,P,heap] mem v mem') :
    ScalarAt mem' heap 4 L P ((25/32:ℝ)*(((1/(2:ℝ)^k)*Num.IPM.alphaPrime m U)/32)^2/50) := by
  have hh := hout.1.2.2.2.2
  change ScalarAt mem' heap 4 L P (1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U))) at hh
  rw [dyadicNormalization_eq] at hh
  simp only [Num.IPM.alphaPrime]
  convert hh using 1
  ring

/-- The common range covers the normalization exponent, including the
factor `25/32` used to make the requested normalization dyadic. -/
theorem selected_normalization_exponent_le_range (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    dyadicNormalizationExponent k (Num.IPM.alphaExponent m U) ≤ ipmRangeExponent m U := by
  have ha := alphaExponent_le_slackRange m U hsize
  unfold dyadicNormalizationExponent ipmRangeExponent
  omega

/-- The selected precision covers the normalization whenever the quality
exponent is at most the slack range exponent. -/
theorem selected_normalization_exponent_le (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    dyadicNormalizationExponent k (Num.IPM.alphaExponent m U) ≤ ipmPrecision m U := by
  have hd := selected_normalization_exponent_le_range m U k hsize hk
  have hp := (ipm_precision_margins m U).2.2.1
  omega

/-- A dyadic quality exponent in the chosen range gives an explicit
lower bound on the product used by all numerical tolerances. -/
theorem dyadic_quality_product_lower (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    1/(2:ℝ)^(2*slackRangeExponent m U) ≤
      (1/(2:ℝ)^k)*Num.IPM.alphaPrime m U := by
  have ha := alphaExponent_le_slackRange m U hsize
  have hp : (2:ℝ)^(k+Num.IPM.alphaExponent m U) ≤
      (2:ℝ)^(2*slackRangeExponent m U) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(2:ℝ)^(k+Num.IPM.alphaExponent m U)) hp
  simpa only [pow_add,one_div_mul_one_div,Num.IPM.alphaPrime] using hh

/-- The common range covers the normalization exponent, including the
factor `25/32` used to make the requested normalization dyadic. -/
theorem quality_normalization_exponent_le_range (m U k : ℕ) (hsize : 2 ≤ m*U) :
    dyadicNormalizationExponent k (Num.IPM.alphaExponent m U) ≤ ipmQualityRangeExponent m U k := by
  have ha := (alphaExponent_le_slackRange m U hsize).trans
    (slackRangeExponent_le_qualitySlackExponent m U k)
  have hk := qualityExponent_le_qualitySlackExponent m U k
  unfold dyadicNormalizationExponent ipmQualityRangeExponent
  omega

/-- The selected precision covers the normalization whenever the quality
exponent widens the slack range. -/
theorem quality_normalization_exponent_le (m U k : ℕ) (hsize : 2 ≤ m*U) :
    dyadicNormalizationExponent k (Num.IPM.alphaExponent m U) ≤ ipmQualityPrecision m U k := by
  have hd := quality_normalization_exponent_le_range m U k hsize
  have hp := (ipm_quality_precision_margins m U k).2.2.1
  omega

/-- A dyadic quality exponent in the chosen range gives an explicit
lower bound on the product used by all numerical tolerances. -/
theorem widened_dyadic_quality_product_lower (m U k : ℕ) (hsize : 2 ≤ m*U) :
    1/(2:ℝ)^(2*qualitySlackExponent m U k) ≤
      (1/(2:ℝ)^k)*Num.IPM.alphaPrime m U := by
  have ha := (alphaExponent_le_slackRange m U hsize).trans
    (slackRangeExponent_le_qualitySlackExponent m U k)
  have hk := qualityExponent_le_qualitySlackExponent m U k
  have hp : (2:ℝ)^(k+Num.IPM.alphaExponent m U) ≤
      (2:ℝ)^(2*qualitySlackExponent m U k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(2:ℝ)^(k+Num.IPM.alphaExponent m U)) hp
  simpa only [pow_add,one_div_mul_one_div,Num.IPM.alphaPrime] using hh

/-- The normalization kernel's fit hypotheses hold together on a real
machine run, including exact fixed-point decoding. -/
theorem normalization_example :
    let p : Program := ⟨normalizationModule 0⟩
    p.IsDeterministic ∧ ∀ ω : ℕ → Bool,
      ∃ o st c,Runs 16 p ω (normalizationBody 1)
        (startState [0,0,8,20,0] (fun _ => 0) 0) o st c ∧
        o.value=8 ∧ ScalarAt st.mem 0 4 8 20 (1/(2:ℝ)^16) ∧ c ≤ 150 := by
  dsimp only
  have hplace : (⟨normalizationModule 0⟩ : Program).HasAt 0 (normalizationModule 0) := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hmet := normalization_meetsContract (by decide : 16 < 2^16) hplace
  constructor
  · exact normalizationModule_noRand 0
  · intro ω
    have hpre : (normalizationContract 16).pre [0,0,8,20,0] (fun _ => 0) := by
      refine ⟨⟨0,0,8,20,0,rfl,by decide,by decide⟩,?_,by decide⟩
      intro x _
      rfl
    obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hmet [0,0,8,20,0] (fun _ => 0) 0 ω
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) hpre
    have he : body=normalizationBody 1 := by simpa [normalizationModule] using hbody.symm
    subst body
    exact ⟨o,st,c,hr,hpost.2,hpost.1.2.2.2.2,hcost⟩

end MinCostFlow.IPM.Machine
