module

public import MinCostFlow.Machine.WideWord.Compile

/-!
# Simulation of guest expressions and call arguments

This file verifies expression evaluation and call-argument marshaling for `compile`:
* `compileConstBits_runs`: materializes `< 2 ^ w'` constants in `≤ 100 * L * w'` host steps.
* `compileBinOp_runs`: runs all 12 guest binary operations in `≤ 750 * L * w'` host steps.
* `compileExpr_runs`: evaluates any guest expression inside `[dstSlot]` using temporaries above
  `tmpSlot` in `≤ 800 * L * w' * e.size` host steps without modifying registers `≠ 8` or trie nodes.
* `compileCallArgs_runs`: evaluates a guest call argument list into the callee's frame in
  `≤ 850 * L * w' * argsSize args + 1` host steps.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Helper arithmetic and frame lemmas -/

theorem two_pow_four_le_of_hw2 {h w : ℕ} (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) :
    16 ≤ 2 ^ w := by
  have : 2 ^ 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using this

theorem slot_end_le_frame {slot slots L : ℕ} (hslot : slot < slots) :
    slot * L + L ≤ slots * L := by
  have h1 : slot + 1 ≤ slots := hslot
  calc slot * L + L = (slot + 1) * L := by ring
    _ ≤ slots * L := Nat.mul_le_mul_right L h1

theorem slot_mul_le_mul {a b L : ℕ} (hab : a ≤ b) : a * L ≤ b * L :=
  Nat.mul_le_mul_right L hab

theorem eval_slotAddr {w : ℕ} {st : State} {rBase baseAddr slot slots L : ℕ}
    (hr : st.regs rBase = baseAddr) (h5 : st.regs 5 = L)
    (hslot : slot < slots) (hslots_w : slots < 2 ^ w) (_hL_w : L < 2 ^ w)
    (hbound : baseAddr + slots * L < 2 ^ w) :
    (slotAddr rBase slot).eval w st = some (baseAddr + slot * L) := by
  have hslot_w : slot < 2 ^ w := lt_trans hslot hslots_w
  have hmul_w : slot * L < 2 ^ w := by
    have : slot * L ≤ slots * L := Nat.mul_le_mul_right L (Nat.le_of_lt hslot)
    omega
  have hadd_w : baseAddr + slot * L < 2 ^ w := by
    have : slot * L ≤ slots * L := Nat.mul_le_mul_right L (Nat.le_of_lt hslot)
    omega
  dsimp only [slotAddr]
  exact Expr.eval_add (by eval_expr)
    (Expr.eval_mul (by simp [Expr.eval, hslot_w]) (by eval_expr) hmul_w) hadd_w

theorem hLh_lt_two_pow_of_scale {L h scale cost w : ℕ}
    (hscale : 1 ≤ scale) (hcost : 1 ≤ cost)
    (hbound : scale * L * 2 ^ h * cost < 2 ^ w) : L * h < 2 ^ w := by
  have hh2h : h < 2 ^ h := Nat.lt_two_pow_self
  have hle1 : L * h ≤ L * 2 ^ h := Nat.mul_le_mul_left L (Nat.le_of_lt hh2h)
  have hle2 : L * 2 ^ h ≤ scale * L * 2 ^ h := by
    calc L * 2 ^ h = 1 * L * 2 ^ h := by ring
      _ ≤ scale * L * 2 ^ h := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hscale)
  have hle3 : scale * L * 2 ^ h ≤ scale * L * 2 ^ h * cost :=
    Nat.le_mul_of_pos_right _ hcost
  omega

theorem expr_eval_lt_two_pow {w' : ℕ} {gst : State} {e : Expr} {v : ℕ}
    (hreg : ∀ r < e.regBound, gst.regs r < 2 ^ w')
    (hmem : ∀ a, gst.mem a < 2 ^ w')
    (he : e.eval w' gst = some v) : v < 2 ^ w' := by
  induction e generalizing v with
  | const k =>
    simp only [Expr.eval] at he
    split_ifs at he with hk
    · cases he; exact hk
  | reg r =>
    simp only [Expr.eval, Option.some.injEq] at he
    subst he
    exact hreg r (by simp [Expr.regBound])
  | load a _ =>
    simp only [Expr.eval, Option.map_eq_some_iff] at he
    rcases he with ⟨addr, _, rfl⟩
    exact hmem addr
  | bin op a b _ _ =>
    simp only [Expr.eval] at he
    cases ha : a.eval w' gst with
    | none => simp [ha] at he
    | some va =>
      cases hb : b.eval w' gst with
      | none => simp [ha, hb] at he
      | some vb =>
        simp only [ha, hb] at he
        split_ifs at he with hlt
        · cases he; exact hlt

theorem evalArgs_lt_two_pow {w' : ℕ} {gst : State} :
    ∀ {args : List Expr} {vs : List ℕ},
      (∀ r < argsRegBound args, gst.regs r < 2 ^ w') →
      (∀ a, gst.mem a < 2 ^ w') →
      evalArgs w' gst args = some vs →
      ∀ v ∈ vs, v < 2 ^ w'
  | [], vs, _, _, h, v, hv => by simp [evalArgs] at h; subst h; simp at hv
  | e :: es, vs, hr, hm, h, v, hv => by
    simp only [evalArgs] at h
    cases he : e.eval w' gst with
    | none => simp [he] at h
    | some u =>
      cases hes : evalArgs w' gst es with
      | none => simp [he, hes] at h
      | some us =>
        simp only [he, hes, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact expr_eval_lt_two_pow
            (fun r hru => hr r (lt_of_lt_of_le hru (by simp [argsRegBound]))) hm he
        · exact evalArgs_lt_two_pow
            (fun r hru => hr r (lt_of_lt_of_le hru (by simp [argsRegBound]))) hm hes v hv

/-! ### Compiled constant bit-construction -/

private theorem foldl_shl1_mod (M : ℕ) :
    ∀ (bits : List ℕ) (acc : ℕ),
      (bits.foldl (fun x b => 2 * x + b) (acc % M)) % M =
        (bits.foldl (fun x b => 2 * x + b) acc) % M
  | [], acc => by simp
  | b :: bs, acc => by
    simp only [List.foldl_cons]
    have h1 : (2 * (acc % M) + b) % M = (2 * acc + b) % M := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    rw [← foldl_shl1_mod M bs (2 * (acc % M) + b), h1, foldl_shl1_mod M bs (2 * acc + b)]

private theorem foldl_compileConstBits_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {arithBase dstSlot framePtr L h : ℕ}
    (hShl : MeetsContract w p (arithBase + idxShl1AddBit) (mwShl1AddBitContract w))
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w)
    (hH2_w : 2 ^ h < 2 ^ w) (hL_w : L < 2 ^ w)
    (hdst_w : framePtr + dstSlot * L + L < 2 ^ w) (hdst_slot_w : dstSlot < 2 ^ w)
    (hmul_w : dstSlot * L < 2 ^ w) :
    ∀ (bits : List ℕ) (accStmt : Stmt) (st₀ : State) (accVal bound : ℕ),
      (∀ b ∈ bits, b ≤ 1) →
      (∃ st₁ c₀, Runs w p ω accStmt st₀ .normal st₁ c₀ ∧
        c₀ ≤ bound ∧
        st₁.regs 2 = framePtr ∧ st₁.regs 5 = L ∧ st₁.regs 7 = 2 ^ h ∧
        (∀ r, r ≠ 8 → st₁.regs r = st₀.regs r) ∧
        LimbsAt st₁.mem (framePtr + dstSlot * L) L h accVal ∧
        ∀ q, q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q →
          st₁.mem q = st₀.mem q) →
      ∃ st' c, Runs w p ω
        (bits.foldl (fun acc b =>
          acc ;; .call 8 (arithBase + idxShl1AddBit)
            [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7]) accStmt)
        st₀ .normal st' c ∧
        st'.regs 2 = framePtr ∧ st'.regs 5 = L ∧ st'.regs 7 = 2 ^ h ∧
        (∀ r, r ≠ 8 → st'.regs r = st₀.regs r) ∧
        LimbsAt st'.mem (framePtr + dstSlot * L) L h
          ((bits.foldl (fun x b => 2 * x + b) accVal) % 2 ^ (L * h)) ∧
        (∀ q, q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q →
          st'.mem q = st₀.mem q) ∧
        c ≤ bound + (38 * L + 26) * bits.length := by
  intro bits
  induction bits with
  | nil =>
    intro accStmt st₀ accVal bound _ hpre
    rcases hpre with ⟨st₁, c₀, hr₁, hc₀, r2, r5, r7, hreg₁, hlim₁, hfr₁⟩
    refine ⟨st₁, c₀, hr₁, r2, r5, r7, hreg₁, ?_, hfr₁, by simpa using hc₀⟩
    simpa [Nat.mod_eq_of_lt hlim₁.lt_pow] using hlim₁
  | cons b bs ih =>
    intro accStmt st₀ accVal bound hbits hpre
    have hb1 : b ≤ 1 := hbits b (by simp)
    have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
    have hb_w : b < 2 ^ w := by omega
    have hbs : ∀ b' ∈ bs, b' ≤ 1 := fun b' hb' => hbits b' (by simp [hb'])
    obtain ⟨st₁, c₀, hr₁, hc₀, r2, r5, r7, hreg₁, hlim₁, hfr₁⟩ := hpre
    have hslot_eval : (slotAddr 2 dstSlot).eval w st₁ = some (framePtr + dstSlot * L) := by
      have hadd_w : framePtr + dstSlot * L < 2 ^ w := by omega
      dsimp only [slotAddr]
      exact Expr.eval_add (by eval_expr)
        (Expr.eval_mul (by simp [Expr.eval, hdst_slot_w]) (by eval_expr) hmul_w) hadd_w
    have hargs : evalArgs w st₁ [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7] =
        some [framePtr + dstSlot * L, b, L, 2 ^ h] :=
      evalArgs_cons hslot_eval (evalArgs_cons (by simp [Expr.eval, hb_w])
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hpre_shl : (mwShl1AddBitContract w).pre
        [framePtr + dstSlot * L, b, L, 2 ^ h] st₁.mem :=
      ⟨framePtr + dstSlot * L, b, L, h, accVal, rfl, hb1, hh, hw2, hdst_w, hlim₁⟩
    obtain ⟨st₂, c₂, v₂, hcall, hpost₂, hv₂, hother₂, hc₂⟩ :=
      runs_call_of_meetsContract (r := 8) hShl hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre_shl ω
    rcases hpost₂ with ⟨dst', b', L', h', heq, _, hlim_fn, hfr₂⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, hp_eq⟩
    have hh_eq : h' = h := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    obtain ⟨_, hlim₂⟩ := hlim_fn accVal hlim₁
    have hr_seq : Runs w p ω
        (accStmt ;; .call 8 (arithBase + idxShl1AddBit)
          [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7])
        st₀ .normal st₂ (c₀ + c₂ + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₀, c₂, hr₁, hcall, rfl⟩)
    have hreg₂ : ∀ r, r ≠ 8 → st₂.regs r = st₀.regs r := fun r hr8 =>
      (hother₂ r hr8).trans (hreg₁ r hr8)
    have hc_step : c₀ + c₂ + 1 ≤ bound + (38 * L + 26) := by
      dsimp only [mwShl1AddBitContract] at hc₂
      simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size_bin, Expr.size_reg,
        Expr.size_const] at hc₂
      omega
    obtain ⟨st', c, hr', r2', r5', r7', hreg', hlim', hfr', hc'⟩ := ih
      (accStmt ;; .call 8 (arithBase + idxShl1AddBit)
        [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7])
      st₀ ((2 * accVal + b) % 2 ^ (L * h)) (bound + (38 * L + 26)) hbs
      ⟨st₂, c₀ + c₂ + 1, hr_seq, hc_step, by rw [hother₂ 2 (by omega), r2],
        by rw [hother₂ 5 (by omega), r5], by rw [hother₂ 7 (by omega), r7],
        hreg₂, hlim₂, fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)⟩
    refine ⟨st', c, hr', r2', r5', r7', hreg', ?_, hfr', ?_⟩
    · simp only [List.foldl_cons]
      rwa [foldl_shl1_mod] at hlim'
    · simp only [List.length_cons]
      have : (38 * L + 26) + (38 * L + 26) * bs.length = (38 * L + 26) * (bs.length + 1) := by ring
      omega

theorem compileConstBits_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {arithBase dstSlot framePtr slots L h w' k : ℕ}
    (hZero : MeetsContract w p (arithBase + idxZero) (mwZeroContract w))
    (hShl : MeetsContract w p (arithBase + idxShl1AddBit) (mwShl1AddBitContract w))
    {st₀ : State}
    (r2 : st₀.regs 2 = framePtr) (r5 : st₀.regs 5 = L) (r7 : st₀.regs 7 = 2 ^ h)
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hk : k < 2 ^ w') (hdst : dstSlot < slots) (hslots_w : slots < 2 ^ w)
    (hL_w : L < 2 ^ w) (hH2_w : 2 ^ h < 2 ^ w) (hframe_w : framePtr + slots * L < 2 ^ w) :
    ∃ st' c, Runs w p ω (compileConstBits arithBase dstSlot k) st₀ .normal st' c ∧
      (∀ r, r ≠ 8 → st'.regs r = st₀.regs r) ∧
      LimbsAt st'.mem (framePtr + dstSlot * L) L h k ∧
      (∀ q, q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q →
        st'.mem q = st₀.mem q) ∧
      c ≤ 100 * L * w' := by
  have hdst_end : framePtr + dstSlot * L + L < 2 ^ w := by
    have := slot_end_le_frame hdst (L := L); omega
  have hdst_slot_w : dstSlot < 2 ^ w := lt_trans hdst hslots_w
  have hmul_w : dstSlot * L < 2 ^ w := by
    have := slot_end_le_frame hdst (L := L); omega
  have hslot_eval : (slotAddr 2 dstSlot).eval w st₀ = some (framePtr + dstSlot * L) :=
    eval_slotAddr r2 r5 hdst hslots_w hL_w hframe_w
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hargs0 : evalArgs w st₀ [slotAddr 2 dstSlot, .reg 5] = some [framePtr + dstSlot * L, L] :=
    evalArgs_cons hslot_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
  have hpre0 : (mwZeroContract w).pre [framePtr + dstSlot * L, L] st₀.mem :=
    ⟨framePtr + dstSlot * L, L, rfl, hw1, hdst_end⟩
  obtain ⟨st₁, c₀, _, hcall0, hpost0, _, hother0, hc₀⟩ :=
    runs_call_of_meetsContract (r := 8) hZero hargs0
      (by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> omega)
      hpre0 ω
  rcases hpost0 with ⟨dst', L', heq0, _, hzero_list, hfr0⟩
  simp only [List.cons.injEq, and_true] at heq0
  rcases heq0 with ⟨rfl, rfl⟩
  have hc0_le : c₀ ≤ 14 * L + 20 := by
    dsimp only [mwZeroContract] at hc₀
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size_bin, Expr.size_reg,
      Expr.size_const] at hc₀
    omega
  have hfold := foldl_compileConstBits_runs hShl hh hw2 hH2_w hL_w hdst_end hdst_slot_w hmul_w
    (bitsMSB k) (.call 8 (arithBase + idxZero) [slotAddr 2 dstSlot, .reg 5])
    st₀ 0 (14 * L + 20)
    (fun b hb => by rcases bitsMSB_mem hb with rfl | rfl <;> omega)
    ⟨st₁, c₀, hcall0, hc0_le, by rw [hother0 2 (by omega), r2],
      by rw [hother0 5 (by omega), r5], by rw [hother0 7 (by omega), r7],
      hother0, limbsAt_zero_iff.mpr hzero_list, hfr0⟩
  rcases hfold with ⟨st', c, hr', _, _, _, hreg', hlim', hfr', hc'⟩
  have hk_lh : k < 2 ^ (L * h) :=
    lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hw'_lh)
  have hlen_w' : (bitsMSB k).length ≤ w' := by
    rw [bitsMSB_length]; exact bitLen_le_of_lt_two_pow hk
  rw [foldl_bitsMSB, Nat.mod_eq_of_lt hk_lh] at hlim'
  refine ⟨st', c, hr', hreg', hlim', hfr', ?_⟩
  have hmul1 : (38 * L + 26) * (bitsMSB k).length ≤ (38 * L + 26) * w' :=
    Nat.mul_le_mul_left _ hlen_w'
  have hL_ge : 14 * L + 20 ≤ 36 * L * w' := by
    have : 14 * L + 20 ≤ 36 * L := by omega
    have : 36 * L ≤ 36 * L * w' := Nat.le_mul_of_pos_right _ hw'1
    omega
  have hw'_ge : (38 * L + 26) * w' ≤ 64 * L * w' := by
    have : 38 * L + 26 ≤ 64 * L := by omega
    calc (38 * L + 26) * w' ≤ (64 * L) * w' := Nat.mul_le_mul_right _ this
      _ = 64 * L * w' := by ring
  have h100 : 36 * L * w' + 64 * L * w' = 100 * L * w' := by ring
  omega

/-! ### Compiled binary operations -/

theorem compileBinOp_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {arithBase aSlot bSlot dstSlot scratchSlot framePtr slots L h w' va vb v : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (op : BinOp) {st₀ : State}
    (r2 : st₀.regs 2 = framePtr) (r5 : st₀.regs 5 = L)
    (r6 : st₀.regs 6 = h) (r7 : st₀.regs 7 = 2 ^ h)
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hLh : L * h < 2 ^ w)
    (ha_slot : aSlot < slots) (hb_slot : bSlot < slots)
    (hdst_slot : dstSlot < slots) (hscr_slot : scratchSlot < slots)
    (hslots_w : slots < 2 ^ w) (hL_w : L < 2 ^ w) (hH_w : h < 2 ^ w) (hH2_w : 2 ^ h < 2 ^ w)
    (hframe_w : framePtr + slots * L < 2 ^ w)
    (hdisj_da : dstSlot ≠ aSlot) (hdisj_db : dstSlot ≠ bSlot)
    (hdisj_sa : scratchSlot ≠ aSlot) (hdisj_sb : scratchSlot ≠ bSlot)
    (hdisj_sd : scratchSlot ≠ dstSlot)
    (hva : LimbsAt st₀.mem (framePtr + aSlot * L) L h va)
    (hvb : LimbsAt st₀.mem (framePtr + bSlot * L) L h vb)
    (hva_lt : va < 2 ^ w') (hvb_lt : vb < 2 ^ w') (hv_lt : v < 2 ^ w')
    (hop : op.eval va vb = v) :
    ∃ st' c, Runs w p ω (compileBinOp arithBase op aSlot bSlot dstSlot scratchSlot) st₀ .normal st' c ∧
      (∀ r, r ≠ 8 → st'.regs r = st₀.regs r) ∧
      LimbsAt st'.mem (framePtr + dstSlot * L) L h v ∧
      (∀ q, (q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q) →
        (q < framePtr + scratchSlot * L ∨ framePtr + scratchSlot * L + L ≤ q) →
        st'.mem q = st₀.mem q) ∧
      c ≤ 750 * L * w' := by
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have h16 : 16 ≤ 2 ^ w := two_pow_four_le_of_hw2 hh hw2
  have hv_lh : v < 2 ^ (L * h) :=
    lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by norm_num) hw'_lh)
  have hdisj_slot : ∀ s₁ s₂, s₁ ≠ s₂ →
      framePtr + s₁ * L + L ≤ framePtr + s₂ * L ∨ framePtr + s₂ * L + L ≤ framePtr + s₁ * L := by
    intro s₁ s₂ hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact Or.inl (by have := slot_end_le_frame hlt (L := L); omega)
    · exact Or.inr (by have := slot_end_le_frame hlt (L := L); omega)
  have ha_end : framePtr + aSlot * L + L < 2 ^ w := by
    have := slot_end_le_frame ha_slot (L := L); omega
  have hb_end : framePtr + bSlot * L + L < 2 ^ w := by
    have := slot_end_le_frame hb_slot (L := L); omega
  have hdst_end : framePtr + dstSlot * L + L < 2 ^ w := by
    have := slot_end_le_frame hdst_slot (L := L); omega
  have hscr_end : framePtr + scratchSlot * L + L < 2 ^ w := by
    have := slot_end_le_frame hscr_slot (L := L); omega
  have ha_eval : (slotAddr 2 aSlot).eval w st₀ = some (framePtr + aSlot * L) :=
    eval_slotAddr r2 r5 ha_slot hslots_w hL_w hframe_w
  have hb_eval : (slotAddr 2 bSlot).eval w st₀ = some (framePtr + bSlot * L) :=
    eval_slotAddr r2 r5 hb_slot hslots_w hL_w hframe_w
  have hdst_eval : (slotAddr 2 dstSlot).eval w st₀ = some (framePtr + dstSlot * L) :=
    eval_slotAddr r2 r5 hdst_slot hslots_w hL_w hframe_w
  have hscr_eval : (slotAddr 2 scratchSlot).eval w st₀ = some (framePtr + scratchSlot * L) :=
    eval_slotAddr r2 r5 hscr_slot hslots_w hL_w hframe_w
  have hLw' : L ≤ L * w' := Nat.le_mul_of_pos_right _ hw'1
  have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
  have h750L : 750 * L ≤ 750 * L * w' := Nat.le_mul_of_pos_right _ hw'1
  cases op with
  | add =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    have hpre : (mwAddContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwAdd_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, hp_eq⟩
    have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    obtain ⟨_, hlim⟩ := hfn va vb hva hvb
    rw [show (va + vb) % 2 ^ (L * h) = v from by simpa [BinOp.eval, ← hop] using Nat.mod_eq_of_lt hv_lh] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwAddContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | sub =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    have hpre : (mwSubContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwSub_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, hp_eq⟩
    have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    have hlim := hfn va vb hva hvb
    rw [show va - vb = v from hop] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwSubContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | mul =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    have hpre : (mwMulContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwMul_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, hp_eq⟩
    have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    have hlim := hfn va vb hva hvb
    rw [show (va * vb) % 2 ^ (L * h) = v from by simpa [BinOp.eval, ← hop] using Nat.mod_eq_of_lt hv_lh] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwMulContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size_bin, Expr.size_reg,
      Expr.size_const] at hc
    rw [memActiveLimbs_eq_activeLimbs hva, memActiveLimbs_eq_activeLimbs hvb] at hc
    have hla : activeLimbs va L h ≤ L := activeLimbs_le va L h
    have hlb : activeLimbs vb L h ≤ w' :=
      le_trans (activeLimbs_le_bitLen hh) (bitLen_le_of_lt_two_pow hvb_lt)
    have hprod : activeLimbs va L h * activeLimbs vb L h ≤ L * w' := Nat.mul_le_mul hla hlb
    have h45 : 45 * (activeLimbs va L h * activeLimbs vb L h) ≤ 45 * (L * w') :=
      Nat.mul_le_mul_left 45 hprod
    have h95 : 95 * L ≤ 95 * (L * w') := Nat.mul_le_mul_left 95 hLw'
    have h70 : 70 ≤ 70 * (L * w') := Nat.le_mul_of_pos_right 70 h1w'
    have h45' : 45 * (L * w') = 45 * L * w' := by ring
    have h95' : 95 * (L * w') = 95 * L * w' := by ring
    have h70' : 70 * (L * w') = 70 * L * w' := by ring
    have h210 : 95 * (L * w') + 45 * (L * w') + 70 * (L * w') ≤ 750 * (L * w') := by
      have : 95 * (L * w') + 45 * (L * w') + 70 * (L * w') = 210 * (L * w') := by ring
      omega
    have h750' : 750 * (L * w') = 750 * L * w' := by ring
    omega
  | div =>
    have hargs : evalArgs w st₀
        [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, slotAddr 2 scratchSlot,
          .reg 5, .reg 6, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L,
          framePtr + scratchSlot * L, L, h, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval (evalArgs_cons hscr_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _)))))))
    have hpre : (mwDivModContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L,
          framePtr + scratchSlot * L, L, h, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L,
        framePtr + scratchSlot * L, L, h, va, vb, rfl, hh, hw2, ha_end, hb_end, hdst_end, hscr_end,
        hdisj_slot dstSlot aSlot hdisj_da, hdisj_slot dstSlot bSlot hdisj_db,
        hdisj_slot scratchSlot aSlot hdisj_sa, hdisj_slot scratchSlot bSlot hdisj_sb,
        (hdisj_slot scratchSlot dstSlot hdisj_sd).symm, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwDivMod_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    obtain ⟨hq_lim, _⟩ := hfn va vb hva hvb
    rw [show va / vb = v from hop] at hq_lim
    refine ⟨st', c, hrun, hother, hq_lim, fun q hqd hqs => hfr q hqd hqs, ?_⟩
    dsimp only [mwDivModContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    rw [memBitLen_eq_bitLen hva] at hc
    have hbl : bitLen va ≤ w' := bitLen_le_of_lt_two_pow hva_lt
    have hmul1 : 280 * L * (bitLen va + 1) ≤ 280 * L * (w' + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul2 : 280 * L * (w' + 1) = 280 * L * w' + 280 * L := by ring
    have h280 : 280 * L ≤ 280 * (L * w') := Nat.mul_le_mul_left 280 hLw'
    have h190 : 190 ≤ 190 * (L * w') := Nat.le_mul_of_pos_right 190 h1w'
    have h280' : 280 * (L * w') = 280 * L * w' := by ring
    have h190' : 190 * (L * w') = 190 * L * w' := by ring
    have h750' : 280 * L * w' + 280 * L * w' + 190 * L * w' = 750 * L * w' := by ring
    omega
  | mod =>
    have hargs : evalArgs w st₀
        [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 scratchSlot, slotAddr 2 dstSlot,
          .reg 5, .reg 6, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + scratchSlot * L,
          framePtr + dstSlot * L, L, h, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hscr_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _)))))))
    have hpre : (mwDivModContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + scratchSlot * L,
          framePtr + dstSlot * L, L, h, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + scratchSlot * L,
        framePtr + dstSlot * L, L, h, va, vb, rfl, hh, hw2, ha_end, hb_end, hscr_end, hdst_end,
        hdisj_slot scratchSlot aSlot hdisj_sa, hdisj_slot scratchSlot bSlot hdisj_sb,
        hdisj_slot dstSlot aSlot hdisj_da, hdisj_slot dstSlot bSlot hdisj_db,
        hdisj_slot scratchSlot dstSlot hdisj_sd, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwDivMod_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    obtain ⟨_, hr_lim⟩ := hfn va vb hva hvb
    rw [show va % vb = v from hop] at hr_lim
    refine ⟨st', c, hrun, hother, hr_lim, fun q hqd hqs => hfr q hqs hqd, ?_⟩
    dsimp only [mwDivModContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    rw [memBitLen_eq_bitLen hva] at hc
    have hbl : bitLen va ≤ w' := bitLen_le_of_lt_two_pow hva_lt
    have hmul1 : 280 * L * (bitLen va + 1) ≤ 280 * L * (w' + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul2 : 280 * L * (w' + 1) = 280 * L * w' + 280 * L := by ring
    have h280 : 280 * L ≤ 280 * (L * w') := Nat.mul_le_mul_left 280 hLw'
    have h190 : 190 ≤ 190 * (L * w') := Nat.le_mul_of_pos_right 190 h1w'
    have h280' : 280 * (L * w') = 280 * L * w' := by ring
    have h190' : 190 * (L * w') = 190 * L * w' := by ring
    have h750' : 280 * L * w' + 280 * L * w' + 190 * L * w' = 750 * L * w' := by ring
    omega
  | lt =>
    have hargs1 : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, .reg 5] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, L] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    have hpre1 : (mwLtContract w).pre [framePtr + aSlot * L, framePtr + bSlot * L, L] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, L, h, va, vb, rfl, hh, hw2, ha_end, hb_end, hva, hvb⟩
    obtain ⟨st₁, c₁, bval, hrun1, hpost1, hv1, hother1, hc1⟩ :=
      runs_call_of_meetsContract (r := 8) (mwLt_of_arithModule hArith) hargs1
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> omega)
        hpre1 ω
    rcases hpost1 with ⟨_, _, _, heq1, hmem1, hfn1⟩
    simp only [List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl, rfl⟩
    have hbv : bval = v := by
      have := hfn1 h va vb hva hvb
      by_cases hlt : va < vb <;> simp_all [BinOp.eval]
    rw [hbv] at hv1
    have r2_1 : st₁.regs 2 = framePtr := by rw [hother1 2 (by omega), r2]
    have r5_1 : st₁.regs 5 = L := by rw [hother1 5 (by omega), r5]
    have r7_1 : st₁.regs 7 = 2 ^ h := by rw [hother1 7 (by omega), r7]
    have hdst_eval1 : (slotAddr 2 dstSlot).eval w st₁ = some (framePtr + dstSlot * L) :=
      eval_slotAddr r2_1 r5_1 hdst_slot hslots_w hL_w hframe_w
    have hargs2 : evalArgs w st₁ [.reg 8, slotAddr 2 dstSlot, .reg 5, .reg 7] =
        some [v, framePtr + dstSlot * L, L, 2 ^ h] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons hdst_eval1
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hv_w : v < 2 ^ w := by
      have : v ≤ 1 := by dsimp only [BinOp.eval] at hop; split_ifs at hop <;> omega
      omega
    have hpre2 : (mwFromHostContract w).pre [v, framePtr + dstSlot * L, L, 2 ^ h] st₁.mem :=
      ⟨v, framePtr + dstSlot * L, L, h, rfl, hh, hw2, hdst_end⟩
    obtain ⟨st₂, c₂, _, hrun2, hpost2, _, hother2, hc2⟩ :=
      runs_call_of_meetsContract (r := 8) (mwFromHost_of_arithModule hArith) hargs2
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre2 ω
    rcases hpost2 with ⟨_, _, _, h', heq2, _, hfh, hfr2⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl, rfl, hp_eq⟩
    have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    refine ⟨st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hrun1, hrun2, rfl⟩),
      fun r hr => (hother2 r hr).trans (hother1 r hr),
      limbsAt_iff_pointwise.mpr ⟨hv_lh, hfh⟩,
      fun q hqd _ => by rw [hfr2 q hqd, hmem1], ?_⟩
    dsimp only [mwLtContract, mwFromHostContract] at hc1 hc2
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc1 hc2
    omega
  | eq =>
    have hargs1 : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, .reg 5] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, L] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    have hpre1 : (mwEqContract w).pre [framePtr + aSlot * L, framePtr + bSlot * L, L] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, L, rfl, hw1, ha_end, hb_end⟩
    obtain ⟨st₁, c₁, bval, hrun1, hpost1, hv1, hother1, hc1⟩ :=
      runs_call_of_meetsContract (r := 8) (mwEq_of_arithModule hArith) hargs1
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> omega)
        hpre1 ω
    rcases hpost1 with ⟨_, _, _, heq1, hmem1, hfn1⟩
    simp only [List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl, rfl⟩
    have hbv : bval = v := by
      have := hfn1
      have hiff : (∀ i < L, st₀.mem (framePtr + aSlot * L + i) = st₀.mem (framePtr + bSlot * L + i)) ↔
          va = vb := by
        constructor
        · intro hall
          have hvb' : LimbsAt st₀.mem (framePtr + aSlot * L) L h vb :=
            limbsAt_iff_pointwise.mpr ⟨hvb.lt_pow, fun i hi => by
              rw [hall i hi]; exact hvb.getElem hi⟩
          exact hva.ext hvb'
        · intro heqv i hi
          subst heqv
          rw [hva.getElem hi, hvb.getElem hi]
      by_cases heqv : va = vb
      · have hall := hiff.mpr heqv
        simp_all [BinOp.eval]
      · have hneq : ¬ ∀ i < L, st₀.mem (framePtr + aSlot * L + i) = st₀.mem (framePtr + bSlot * L + i) :=
          mt hiff.mp heqv
        simp_all [BinOp.eval]
    rw [hbv] at hv1
    have r2_1 : st₁.regs 2 = framePtr := by rw [hother1 2 (by omega), r2]
    have r5_1 : st₁.regs 5 = L := by rw [hother1 5 (by omega), r5]
    have r7_1 : st₁.regs 7 = 2 ^ h := by rw [hother1 7 (by omega), r7]
    have hdst_eval1 : (slotAddr 2 dstSlot).eval w st₁ = some (framePtr + dstSlot * L) :=
      eval_slotAddr r2_1 r5_1 hdst_slot hslots_w hL_w hframe_w
    have hargs2 : evalArgs w st₁ [.reg 8, slotAddr 2 dstSlot, .reg 5, .reg 7] =
        some [v, framePtr + dstSlot * L, L, 2 ^ h] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons hdst_eval1
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hv_w : v < 2 ^ w := by
      have : v ≤ 1 := by dsimp only [BinOp.eval] at hop; split_ifs at hop <;> omega
      omega
    have hpre2 : (mwFromHostContract w).pre [v, framePtr + dstSlot * L, L, 2 ^ h] st₁.mem :=
      ⟨v, framePtr + dstSlot * L, L, h, rfl, hh, hw2, hdst_end⟩
    obtain ⟨st₂, c₂, _, hrun2, hpost2, _, hother2, hc2⟩ :=
      runs_call_of_meetsContract (r := 8) (mwFromHost_of_arithModule hArith) hargs2
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre2 ω
    rcases hpost2 with ⟨_, _, _, h', heq2, _, hfh, hfr2⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl, rfl, hp_eq⟩
    have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
    cases hh_eq
    refine ⟨st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hrun1, hrun2, rfl⟩),
      fun r hr => (hother2 r hr).trans (hother1 r hr),
      limbsAt_iff_pointwise.mpr ⟨hv_lh, hfh⟩,
      fun q hqd _ => by rw [hfr2 q hqd, hmem1], ?_⟩
    dsimp only [mwEqContract, mwFromHostContract] at hc1 hc2
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc1 hc2
    omega
  | and =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hpre : (mwBitOpContract w .and).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwAnd_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    have hlim := hfn h va vb hva hvb
    rw [show BinOp.and.eval va vb = v from hop] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwBitOpContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | or =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hpre : (mwBitOpContract w .or).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwOr_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    have hlim := hfn h va vb hva hvb
    rw [show BinOp.or.eval va vb = v from hop] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwBitOpContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | xor =>
    have hargs : evalArgs w st₀ [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hpre : (mwBitOpContract w .xor).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwXor_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    have hlim := hfn h va vb hva hvb
    rw [show BinOp.xor.eval va vb = v from hop] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwBitOpContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | shiftLeft =>
    have hargs : evalArgs w st₀
        [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 6, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _))))))
    have hpre : (mwShiftLeftContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, hLh, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwShiftLeft_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    have hlim := hfn va vb hva hvb
    rw [show (va <<< vb) % 2 ^ (L * h) = v from by simpa [BinOp.eval, ← hop] using Nat.mod_eq_of_lt hv_lh] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwShiftLeftContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega
  | shiftRight =>
    have hargs : evalArgs w st₀
        [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 6, .reg 7] =
        some [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, 2 ^ h] :=
      evalArgs_cons ha_eval (evalArgs_cons hb_eval (evalArgs_cons hdst_eval
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _))))))
    have hpre : (mwShiftRightContract w).pre
        [framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, 2 ^ h] st₀.mem :=
      ⟨framePtr + aSlot * L, framePtr + bSlot * L, framePtr + dstSlot * L, L, h, va, vb,
        rfl, hh, hw2, hLh, ha_end, hb_end, hdst_end, hdisj_slot dstSlot aSlot hdisj_da,
        hdisj_slot dstSlot bSlot hdisj_db, hva, hvb⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwShiftRight_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, _, heq, _, hfn, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    have hlim := hfn va vb hva hvb
    rw [show va >>> vb = v from hop] at hlim
    refine ⟨st', c, hrun, hother, hlim, fun q hq _ => hfr q hq, ?_⟩
    dsimp only [mwShiftRightContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc
    omega

/-! ### Compiled guest expression evaluation -/

theorem compileExpr_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {arithBase trieBase w' L h ctrl hp root framePtr regB slots : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt trieBase (trieModule arithBase))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hLh : L * h < 2 ^ w)
    (hslots_w : slots < 2 ^ w) (hL_w : L < 2 ^ w) (hH_w : h < 2 ^ w) (hH2_w : 2 ^ h < 2 ^ w)
    (hhp_w : hp < 2 ^ w) (hctrl_frame : ctrl < framePtr)
    (hframe_w : framePtr + slots * L < 2 ^ w) :
    ∀ (e : Expr) (dstSlot tmpSlot v : ℕ) (st : State) (gst : State),
      e.eval w' gst = some v →
      e.regBound ≤ regB →
      regB ≤ dstSlot → dstSlot < tmpSlot → tmpSlot + exprTempDepth e ≤ slots →
      st.regs 2 = framePtr → st.regs 3 = ctrl → st.regs 5 = L → st.regs 6 = h → st.regs 7 = 2 ^ h →
      st.mem ctrl = root →
      Subtrie st.mem L h hp L root gst.mem →
      (∀ q, InTrie st.mem L h L root q → q < framePtr ∨ framePtr + slots * L ≤ q) →
      (∀ r < regB, gst.regs r < 2 ^ w') →
      (∀ r < regB, LimbsAt st.mem (framePtr + r * L) L h (gst.regs r)) →
      (∀ a, gst.mem a < 2 ^ w') →
      ∃ st' c, Runs w p ω (compileExpr arithBase trieBase dstSlot tmpSlot e) st .normal st' c ∧
        (∀ r, r ≠ 8 → st'.regs r = st.regs r) ∧
        LimbsAt st'.mem (framePtr + dstSlot * L) L h v ∧
        (∀ q, (q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q) →
          (q < framePtr + tmpSlot * L ∨ framePtr + (tmpSlot + exprTempDepth e) * L ≤ q) →
          st'.mem q = st.mem q) ∧
        c ≤ 800 * L * w' * e.size := by
  intro e
  induction e with
  | const k =>
    intro dstSlot tmpSlot v st gst he _ _ hdt hts r2 r3 r5 r6 r7 _ _ _ _ _ _
    simp only [Expr.eval] at he
    split_ifs at he with hk
    · cases he
      obtain ⟨st', c, hrun, hreg, hlim, hfr, hc⟩ := compileConstBits_runs
        (dstSlot := dstSlot) (slots := slots)
        (mwZero_of_arithModule hArith) (mwShl1AddBit_of_arithModule hArith)
        r2 r5 r7 hL1 hh hw2 hw'1 hw'_lh hk (by omega) hslots_w hL_w hH2_w hframe_w
      refine ⟨st', c, hrun, hreg, hlim, fun q hqd _ => hfr q hqd, ?_⟩
      simp only [Expr.size]
      have h800L : 800 * L ≤ 800 * L * w' := Nat.le_mul_of_pos_right _ hw'1
      have h100 : 100 * L * w' ≤ 800 * L * w' := Nat.mul_le_mul_right _ (by omega)
      omega
  | reg r =>
    intro dstSlot tmpSlot v st gst he hrb hrd hdt hts r2 r3 r5 r6 r7 _ _ _ hreg_lt hreg_lim _
    simp only [Expr.eval, Option.some.injEq] at he
    subst he
    simp only [Expr.regBound] at hrb
    have hr_regB : r < regB := by omega
    have hr_slots : r < slots := by omega
    have hdst_slots : dstSlot < slots := by omega
    have hr_eval : (slotAddr 2 r).eval w st = some (framePtr + r * L) :=
      eval_slotAddr r2 r5 hr_slots hslots_w hL_w hframe_w
    have hdst_eval : (slotAddr 2 dstSlot).eval w st = some (framePtr + dstSlot * L) :=
      eval_slotAddr r2 r5 hdst_slots hslots_w hL_w hframe_w
    have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
    have h16 : 16 ≤ 2 ^ w := two_pow_four_le_of_hw2 hh hw2
    have hargs : evalArgs w st [slotAddr 2 r, slotAddr 2 dstSlot, .reg 5] =
        some [framePtr + r * L, framePtr + dstSlot * L, L] :=
      evalArgs_cons hr_eval (evalArgs_cons hdst_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    have hr_end : framePtr + r * L + L < 2 ^ w := by
      have := slot_end_le_frame hr_slots (L := L); omega
    have hdst_end : framePtr + dstSlot * L + L < 2 ^ w := by
      have := slot_end_le_frame hdst_slots (L := L); omega
    have hr_lt_dst : framePtr + r * L + L ≤ framePtr + dstSlot * L := by
      have := slot_end_le_frame (by omega : r < dstSlot) (L := L); omega
    have hpre : (mwCopyContract w).pre [framePtr + r * L, framePtr + dstSlot * L, L] st.mem :=
      ⟨framePtr + r * L, framePtr + dstSlot * L, L, rfl, hw1, hr_end, hdst_end, Or.inr (Or.inl hr_lt_dst)⟩
    obtain ⟨st', c, _, hrun, hpost, _, hother, hc⟩ :=
      runs_call_of_meetsContract (r := 8) (mwCopy_of_arithModule hArith) hargs
        (by
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, heq, _, hcp, hfr⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    have hlim_r := hreg_lim r hr_regB
    have hv_lh : gst.regs r < 2 ^ (L * h) :=
      lt_of_lt_of_le (hreg_lt r hr_regB) (Nat.pow_le_pow_right (by norm_num) hw'_lh)
    refine ⟨st', c, hrun, hother,
      limbsAt_iff_pointwise.mpr ⟨hv_lh, fun i hi => by rw [hcp i hi]; exact hlim_r.getElem hi⟩,
      fun q hqd _ => hfr q hqd, ?_⟩
    dsimp only [mwCopyContract] at hc
    simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc ⊢
    have h800L : 800 * L ≤ 800 * L * w' := Nat.le_mul_of_pos_right _ hw'1
    omega
  | load a iha =>
    intro dstSlot tmpSlot v st gst he hrb hrd hdt hts r2 r3 r5 r6 r7 hm_ctrl hsub htrie_disj
      hreg_lt hreg_lim hmem_lt
    simp only [Expr.eval, Option.map_eq_some_iff] at he
    rcases he with ⟨addr, ha_eval, rfl⟩
    have ha_lt : addr < 2 ^ w' := expr_eval_lt_two_pow (e := a)
      (fun r hr => hreg_lt r (lt_of_lt_of_le hr hrb)) hmem_lt ha_eval
    obtain ⟨st₁, c₁, hr₁, hreg₁, hlim₁, hfr₁, hc₁⟩ :=
      iha dstSlot tmpSlot addr st gst ha_eval hrb hrd hdt hts
        r2 r3 r5 r6 r7 hm_ctrl hsub htrie_disj hreg_lt hreg_lim hmem_lt
    have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), r2]
    have r3_1 : st₁.regs 3 = ctrl := by rw [hreg₁ 3 (by omega), r3]
    have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), r5]
    have hctrl_w : ctrl < 2 ^ w := by omega
    have hroot_w : root < 2 ^ w := subtrie_root_lt hsub hhp_w (one_lt_two_pow_of_le hh hw2)
    have hst1_ctrl : st₁.mem ctrl = root := by
      have hne_d : ctrl < framePtr + dstSlot * L := by omega
      have hne_t : ctrl < framePtr + tmpSlot * L := by omega
      rw [hfr₁ ctrl (Or.inl hne_d) (Or.inl hne_t), hm_ctrl]
    have hload : (Expr.load (.reg 3)).eval w st₁ = some root :=
      Expr.eval_load_of_eq (by eval_expr) hst1_ctrl
    set st₂ : State := { mem := st₁.mem, regs := Function.update st₁.regs 8 root, pos := st₁.pos }
    have r2_2 : st₂.regs 2 = framePtr := by dsimp only [st₂]; rw [Function.update_of_ne (by omega), r2_1]
    have r5_2 : st₂.regs 5 = L := by dsimp only [st₂]; rw [Function.update_of_ne (by omega), r5_1]
    have hdst_slots : dstSlot < slots := by omega
    have hdst_eval : (slotAddr 2 dstSlot).eval w st₂ = some (framePtr + dstSlot * L) :=
      eval_slotAddr r2_2 r5_2 hdst_slots hslots_w hL_w hframe_w
    have hargs : evalArgs w st₂ [.reg 8, slotAddr 2 dstSlot, slotAddr 2 dstSlot, .reg 5] =
        some [root, framePtr + dstSlot * L, framePtr + dstSlot * L, L] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons hdst_eval
        (evalArgs_cons hdst_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hdst_end : framePtr + dstSlot * L + L < 2 ^ w := by
      have := slot_end_le_frame hdst_slots (L := L); omega
    have hts_a : tmpSlot + exprTempDepth a ≤ slots := by simpa [exprTempDepth] using hts
    have hdisj_tr : ∀ q, InTrie st₁.mem L h L root q →
        q < framePtr + dstSlot * L ∨ framePtr + dstSlot * L + L ≤ q := by
      intro q hq
      have hq' := (inTrie_congr_mem L root (fun p hp' => by
        rcases htrie_disj p hp' with hlt | hge
        · exact hfr₁ p (Or.inl (by omega)) (Or.inl (by omega))
        · have hd_lt : framePtr + dstSlot * L + L ≤ framePtr + slots * L := by
            have := slot_end_le_frame hdst_slots (L := L); omega
          have ht_lt : framePtr + (tmpSlot + exprTempDepth a) * L ≤ framePtr + slots * L := by
            have := slot_mul_le_mul hts_a (L := L); omega
          exact hfr₁ p (Or.inr (by omega)) (Or.inr (by omega))) q).mp hq
      rcases htrie_disj q hq' with hlt | hge
      · exact Or.inl (by omega)
      · have hd_lt : framePtr + dstSlot * L + L ≤ framePtr + slots * L := by
          have := slot_end_le_frame hdst_slots (L := L); omega
        exact Or.inr (by omega)
    have hsub₁ : Subtrie st₁.mem L h hp L root gst.mem := by
      refine subtrie_congr_mem (fun q hq => ?_) hsub
      rcases htrie_disj q hq with hlt | hge
      · exact hfr₁ q (Or.inl (by omega)) (Or.inl (by omega))
      · have hd_lt : framePtr + dstSlot * L + L ≤ framePtr + slots * L := by
          have := slot_end_le_frame hdst_slots (L := L); omega
        have ht_lt : framePtr + (tmpSlot + exprTempDepth a) * L ≤ framePtr + slots * L := by
          have := slot_mul_le_mul hts_a (L := L); omega
        exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
    have hpre : (trieReadContract w).pre [root, framePtr + dstSlot * L, framePtr + dstSlot * L, L] st₂.mem :=
      ⟨root, framePtr + dstSlot * L, framePtr + dstSlot * L, L, h, hp, gst.mem, addr,
        rfl, hh, hw2, hhp_w, hdst_end, hdst_end, hdisj_tr, hsub₁, hlim₁⟩
    obtain ⟨st₃, c₂, _, hcall, hpost, _, hother, hc₂⟩ :=
      runs_call_of_meetsContract (r := 8) (trieRead_of_trieModule hArith hTrie) hargs
        (by
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> omega)
        hpre ω
    rcases hpost with ⟨_, _, _, _, heq, _, htr_fn, hfr₂⟩
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    have hlim₃ := htr_fn h hp gst.mem addr hsub₁ hlim₁
    have hass : Runs w p ω (.assign 8 (.load (.reg 3))) st₁ .normal st₂ 3 :=
      runs_assign_iff.mpr ⟨root, hload, rfl, rfl, rfl⟩
    have hcomb : Runs w p ω (compileExpr arithBase trieBase dstSlot tmpSlot (.load a))
        st .normal st₃ (c₁ + (3 + c₂ + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, 3 + c₂ + 1, hr₁,
        runs_seq_iff.mpr (Or.inr ⟨st₂, 3, c₂, hass, hcall, rfl⟩), rfl⟩)
    refine ⟨st₃, _, hcomb, fun r hr => ?_, hlim₃, fun q hqd hqt => ?_, ?_⟩
    · rw [hother r hr]
      dsimp only [st₂]
      rw [Function.update_of_ne hr]
      exact hreg₁ r hr
    · rw [hfr₂ q hqd]
      exact hfr₁ q hqd (by simpa [exprTempDepth] using hqt)
    · dsimp only [trieReadContract] at hc₂
      simp only [argsSize_cons, argsSize_nil, slotAddr, Expr.size] at hc₂ ⊢
      have h16 : 16 ≤ 2 ^ w := two_pow_four_le_of_hw2 hh hw2
      have h800L : 800 * L ≤ 800 * L * w' := Nat.le_mul_of_pos_right _ hw'1
      have hdist : 800 * L * w' * (a.size + 1) = 800 * L * w' * a.size + 800 * L * w' := by ring
      omega
  | bin op a b iha ihb =>
    intro dstSlot tmpSlot v st gst he hrb hrd hdt hts r2 r3 r5 r6 r7 hm_ctrl hsub htrie_disj
      hreg_lt hreg_lim hmem_lt
    simp only [Expr.eval] at he
    cases ha : a.eval w' gst with
    | none => simp [ha] at he
    | some va =>
      cases hb : b.eval w' gst with
      | none => simp [ha, hb] at he
      | some vb =>
        simp only [ha, hb] at he
        split_ifs at he with hv_check
        · cases he
          have hva_lt : va < 2 ^ w' := expr_eval_lt_two_pow
            (fun r hr => hreg_lt r (by simp [Expr.regBound] at hrb; omega)) hmem_lt ha
          have hvb_lt : vb < 2 ^ w' := expr_eval_lt_two_pow
            (fun r hr => hreg_lt r (by simp [Expr.regBound] at hrb; omega)) hmem_lt hb
          have ha_rb : a.regBound ≤ regB := by simp [Expr.regBound] at hrb; omega
          have hb_rb : b.regBound ≤ regB := by simp [Expr.regBound] at hrb; omega
          have ha_ts : tmpSlot + 3 + exprTempDepth a ≤ slots := by
            simp only [exprTempDepth] at hts; omega
          have hb_ts : tmpSlot + 3 + exprTempDepth b ≤ slots := by
            simp only [exprTempDepth] at hts; omega
          obtain ⟨st₁, c₁, hr₁, hreg₁, hlim_a, hfr₁, hc₁⟩ :=
            iha tmpSlot (tmpSlot + 3) va st gst ha ha_rb (by omega) (by omega) ha_ts
              r2 r3 r5 r6 r7 hm_ctrl hsub htrie_disj hreg_lt hreg_lim hmem_lt
          have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), r2]
          have r3_1 : st₁.regs 3 = ctrl := by rw [hreg₁ 3 (by omega), r3]
          have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), r5]
          have r6_1 : st₁.regs 6 = h := by rw [hreg₁ 6 (by omega), r6]
          have r7_1 : st₁.regs 7 = 2 ^ h := by rw [hreg₁ 7 (by omega), r7]
          have hm1_ctrl : st₁.mem ctrl = root := by
            rw [hfr₁ ctrl (Or.inl (by omega)) (Or.inl (by omega)), hm_ctrl]
          have hfr_slots₁ : ∀ q, q < framePtr + tmpSlot * L ∨ framePtr + slots * L ≤ q →
              st₁.mem q = st.mem q := by
            intro q hq
            rcases hq with hlt | hge
            · exact hfr₁ q (Or.inl hlt) (Or.inl (by have := slot_mul_le_mul (by omega : tmpSlot ≤ tmpSlot + 3) (L := L); omega))
            · have : framePtr + tmpSlot * L + L ≤ framePtr + slots * L := by
                have := slot_end_le_frame (by omega : tmpSlot < slots) (L := L); omega
              have : framePtr + (tmpSlot + 3 + exprTempDepth a) * L ≤ framePtr + slots * L := by
                have := slot_mul_le_mul ha_ts (L := L); omega
              exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
          have hsub₁ : Subtrie st₁.mem L h hp L root gst.mem := by
            refine subtrie_congr_mem (fun q hq => ?_) hsub
            rcases htrie_disj q hq with hlt | hge
            · exact hfr_slots₁ q (Or.inl (by omega))
            · exact hfr_slots₁ q (Or.inr hge)
          have htrie_disj₁ : ∀ q, InTrie st₁.mem L h L root q →
              q < framePtr ∨ framePtr + slots * L ≤ q := by
            intro q hq
            rw [inTrie_congr_mem L root (fun p hp' => by
              rcases htrie_disj p hp' with hlt | hge
              · exact hfr_slots₁ p (Or.inl (by omega))
              · exact hfr_slots₁ p (Or.inr hge)) q] at hq
            exact htrie_disj q hq
          have hreg_lim₁ : ∀ r < regB, LimbsAt st₁.mem (framePtr + r * L) L h (gst.regs r) := by
            intro r hr
            refine (hreg_lim r hr).congr fun q hq1 hq2 => ?_
            have hr_lt_tmp : r * L + L ≤ tmpSlot * L := slot_end_le_frame (by omega)
            exact hfr_slots₁ q (Or.inl (by omega))
          obtain ⟨st₂, c₂, hr₂, hreg₂, hlim_b, hfr₂, hc₂⟩ :=
            ihb (tmpSlot + 1) (tmpSlot + 3) vb st₁ gst hb hb_rb (by omega) (by omega) hb_ts
              r2_1 r3_1 r5_1 r6_1 r7_1 hm1_ctrl hsub₁ htrie_disj₁ hreg_lt hreg_lim₁ hmem_lt
          have hlim_a₂ : LimbsAt st₂.mem (framePtr + tmpSlot * L) L h va := by
            refine hlim_a.congr fun q hq1 hq2 => ?_
            have h1 : tmpSlot * L + L ≤ (tmpSlot + 1) * L := slot_end_le_frame (by omega)
            have h2 : tmpSlot * L + L ≤ (tmpSlot + 3) * L := slot_end_le_frame (by omega)
            exact hfr₂ q (Or.inl (by omega)) (Or.inl (by omega))
          have r2_2 : st₂.regs 2 = framePtr := by rw [hreg₂ 2 (by omega), r2_1]
          have r5_2 : st₂.regs 5 = L := by rw [hreg₂ 5 (by omega), r5_1]
          have r6_2 : st₂.regs 6 = h := by rw [hreg₂ 6 (by omega), r6_1]
          have r7_2 : st₂.regs 7 = 2 ^ h := by rw [hreg₂ 7 (by omega), r7_1]
          have htmp_slots : tmpSlot + 3 ≤ slots := by
            simp only [exprTempDepth] at hts; omega
          obtain ⟨st₃, c₃, hbin, hreg₃, hlim_res, hfr₃, hc₃⟩ :=
            compileBinOp_runs (aSlot := tmpSlot) (bSlot := tmpSlot + 1)
              (dstSlot := dstSlot) (scratchSlot := tmpSlot + 2) (slots := slots)
              hArith op r2_2 r5_2 r6_2 r7_2 hL1 hh hw2 hw'1 hw'_lh hLh
              (by omega) (by omega) (by omega) (by omega) hslots_w hL_w hH_w hH2_w hframe_w
              (by omega) (by omega) (by omega) (by omega) (by omega)
              hlim_a₂ hlim_b hva_lt hvb_lt hv_check rfl
          have hr_final : Runs w p ω (compileExpr arithBase trieBase dstSlot tmpSlot (.bin op a b))
              st .normal st₃ (c₁ + (c₂ + c₃ + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + c₃ + 1, hr₁,
              runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃, hr₂, hbin, rfl⟩), rfl⟩)
          refine ⟨st₃, _, hr_final,
            fun r hr => (hreg₃ r hr).trans ((hreg₂ r hr).trans (hreg₁ r hr)),
            hlim_res, fun q hqd hqt => ?_, ?_⟩
          · have hq_not_tmp : q < framePtr + tmpSlot * L ∨ framePtr + (tmpSlot + 1) * L ≤ q := by
              rcases hqt with hlt | hge
              · exact Or.inl hlt
              · have := slot_mul_le_mul (by simp only [exprTempDepth]; omega :
                  tmpSlot + 1 ≤ tmpSlot + exprTempDepth (.bin op a b)) (L := L)
                exact Or.inr (by omega)
            have hq_not_t1 : q < framePtr + (tmpSlot + 1) * L ∨ framePtr + (tmpSlot + 2) * L ≤ q := by
              rcases hqt with hlt | hge
              · have := slot_mul_le_mul (by omega : tmpSlot ≤ tmpSlot + 1) (L := L)
                exact Or.inl (by omega)
              · have := slot_mul_le_mul (by simp only [exprTempDepth]; omega :
                  tmpSlot + 2 ≤ tmpSlot + exprTempDepth (.bin op a b)) (L := L)
                exact Or.inr (by omega)
            have hq_not_t2 : q < framePtr + (tmpSlot + 2) * L ∨ framePtr + (tmpSlot + 3) * L ≤ q := by
              rcases hqt with hlt | hge
              · have := slot_mul_le_mul (by omega : tmpSlot ≤ tmpSlot + 2) (L := L)
                exact Or.inl (by omega)
              · have := slot_mul_le_mul (by simp only [exprTempDepth]; omega :
                  tmpSlot + 3 ≤ tmpSlot + exprTempDepth (.bin op a b)) (L := L)
                exact Or.inr (by omega)
            have hq_not_t3a : q < framePtr + (tmpSlot + 3) * L ∨
                framePtr + (tmpSlot + 3 + exprTempDepth a) * L ≤ q := by
              rcases hqt with hlt | hge
              · have := slot_mul_le_mul (by omega : tmpSlot ≤ tmpSlot + 3) (L := L)
                exact Or.inl (by omega)
              · simp only [exprTempDepth] at hge
                have := slot_mul_le_mul (by omega : tmpSlot + 3 + exprTempDepth a ≤ tmpSlot + (3 + max (exprTempDepth a) (exprTempDepth b))) (L := L)
                exact Or.inr (by omega)
            have hq_not_t3b : q < framePtr + (tmpSlot + 3) * L ∨
                framePtr + (tmpSlot + 3 + exprTempDepth b) * L ≤ q := by
              rcases hqt with hlt | hge
              · have := slot_mul_le_mul (by omega : tmpSlot ≤ tmpSlot + 3) (L := L)
                exact Or.inl (by omega)
              · simp only [exprTempDepth] at hge
                have := slot_mul_le_mul (by omega : tmpSlot + 3 + exprTempDepth b ≤ tmpSlot + (3 + max (exprTempDepth a) (exprTempDepth b))) (L := L)
                exact Or.inr (by omega)
            have hq_tmp_end : framePtr + tmpSlot * L + L = framePtr + (tmpSlot + 1) * L := by ring
            have hq_t1_end : framePtr + (tmpSlot + 1) * L + L = framePtr + (tmpSlot + 2) * L := by ring
            have hq_t2_end : framePtr + (tmpSlot + 2) * L + L = framePtr + (tmpSlot + 3) * L := by ring
            rw [hfr₃ q hqd (by rwa [hq_t2_end]), hfr₂ q (by rwa [hq_t1_end]) hq_not_t3b,
              hfr₁ q (by rwa [hq_tmp_end]) hq_not_t3a]
          · simp only [Expr.size]
            have hdist : 800 * L * w' * (a.size + b.size + 1) =
                800 * L * w' * a.size + 800 * L * w' * b.size + 800 * L * w' := by ring
            have h750 : 750 * L * w' + 2 ≤ 800 * L * w' := by
              have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
              have : 750 * (L * w') + 2 ≤ 800 * (L * w') := by omega
              have h750' : 750 * (L * w') = 750 * L * w' := by ring
              have h800' : 800 * (L * w') = 800 * L * w' := by ring
              omega
            omega

/-! ### Compiled call argument marshaling -/

theorem compileCallArgs_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {arithBase trieBase w' L h ctrl hp root framePtr calleeFrame regB slots rCallee : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt trieBase (trieModule arithBase))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hLh : L * h < 2 ^ w)
    (hslots_w : slots < 2 ^ w) (hL_w : L < 2 ^ w) (hH_w : h < 2 ^ w) (hH2_w : 2 ^ h < 2 ^ w)
    (hhp_w : hp < 2 ^ w) (hctrl_frame : ctrl < framePtr)
    (hframe_w : framePtr + slots * L < 2 ^ w) (hcallee_w : calleeFrame + slots * L < 2 ^ w)
    (hfc_disj : framePtr + slots * L ≤ calleeFrame)
    (hrC8 : rCallee ≠ 8) (hreg_slots : regB + 1 ≤ slots) :
    ∀ (args : List Expr) (idx : ℕ) (vs : List ℕ) (st : State) (gst : State),
      evalArgs w' gst args = some vs →
      argsRegBound args ≤ regB →
      argsTempDepth args + 1 ≤ slots - regB →
      idx + args.length ≤ regB →
      st.regs 2 = framePtr → st.regs 3 = ctrl → st.regs 5 = L → st.regs 6 = h → st.regs 7 = 2 ^ h →
      st.regs rCallee = calleeFrame →
      st.mem ctrl = root →
      Subtrie st.mem L h hp L root gst.mem →
      (∀ q, InTrie st.mem L h L root q →
        (q < framePtr ∨ framePtr + slots * L ≤ q) ∧
        (q < calleeFrame ∨ calleeFrame + slots * L ≤ q)) →
      (∀ r < regB, gst.regs r < 2 ^ w') →
      (∀ r < regB, LimbsAt st.mem (framePtr + r * L) L h (gst.regs r)) →
      (∀ a, gst.mem a < 2 ^ w') →
      ∃ st' c, Runs w p ω (compileCallArgs arithBase trieBase regB rCallee idx args) st .normal st' c ∧
        (∀ r, r ≠ 8 → st'.regs r = st.regs r) ∧
        (∀ k (hk : k < vs.length), LimbsAt st'.mem (calleeFrame + (idx + k) * L) L h vs[k]) ∧
        (∀ q, (q < framePtr + regB * L ∨ framePtr + slots * L ≤ q) →
          (q < calleeFrame + idx * L ∨ calleeFrame + (idx + args.length) * L ≤ q) →
          st'.mem q = st.mem q) ∧
        c ≤ 850 * L * w' * argsSize args + 1 := by
  intro args
  induction args with
  | nil =>
    intro idx vs st gst hargs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    simp only [evalArgs, Option.some.injEq] at hargs
    subst hargs
    refine ⟨st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, fun _ _ => rfl,
      fun _ hk => by simp at hk, fun _ _ _ => rfl, by simp [argsSize]⟩
  | cons e es ih =>
    intro idx vs st gst hargs hrb hts hid r2 r3 r5 r6 r7 hrCal hm_ctrl hsub
      htrie_disj hreg_lt hreg_lim hmem_lt
    simp only [evalArgs] at hargs
    cases he_v : e.eval w' gst with
    | none => simp [he_v] at hargs
    | some v =>
      cases hes_v : evalArgs w' gst es with
      | none => simp [he_v, hes_v] at hargs
      | some vs' =>
        simp only [he_v, hes_v, Option.some.injEq] at hargs
        subst hargs
        have he_rb : e.regBound ≤ regB := by simp [argsRegBound] at hrb; omega
        have hes_rb : argsRegBound es ≤ regB := by simp [argsRegBound] at hrb; omega
        have he_ts : regB + 1 + exprTempDepth e ≤ slots := by
          simp only [argsTempDepth] at hts; omega
        have hes_ts : argsTempDepth es + 1 ≤ slots - regB := by
          simp only [argsTempDepth] at hts; omega
        have htrie_disj_f : ∀ q, InTrie st.mem L h L root q →
            q < framePtr ∨ framePtr + slots * L ≤ q := fun q hq => (htrie_disj q hq).1
        have hv_lt : v < 2 ^ w' := expr_eval_lt_two_pow
          (fun r hr => hreg_lt r (by omega)) hmem_lt he_v
        have hv_lh : v < 2 ^ (L * h) :=
          lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by norm_num) hw'_lh)
        obtain ⟨st₁, c₁, hr₁, hreg₁, hlim₁, hfr₁, hc₁⟩ :=
          compileExpr_runs hArith hTrie hL1 hh hw2 hw'1 hw'_lh hLh hslots_w hL_w hH_w hH2_w
            hhp_w hctrl_frame hframe_w e regB (regB + 1) v st gst he_v he_rb (le_refl _)
            (by omega) he_ts r2 r3 r5 r6 r7 hm_ctrl hsub htrie_disj_f hreg_lt hreg_lim hmem_lt
        have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), r2]
        have r3_1 : st₁.regs 3 = ctrl := by rw [hreg₁ 3 (by omega), r3]
        have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), r5]
        have r6_1 : st₁.regs 6 = h := by rw [hreg₁ 6 (by omega), r6]
        have r7_1 : st₁.regs 7 = 2 ^ h := by rw [hreg₁ 7 (by omega), r7]
        have hrC_1 : st₁.regs rCallee = calleeFrame := by rw [hreg₁ rCallee hrC8, hrCal]
        have hsrc_eval : (slotAddr 2 regB).eval w st₁ = some (framePtr + regB * L) :=
          eval_slotAddr r2_1 r5_1 (by omega) hslots_w hL_w hframe_w
        have hdst_eval : (slotAddr rCallee idx).eval w st₁ = some (calleeFrame + idx * L) :=
          eval_slotAddr hrC_1 r5_1 (by simp at hid; omega) hslots_w hL_w hcallee_w
        have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
        have hargs_cp : evalArgs w st₁ [slotAddr 2 regB, slotAddr rCallee idx, .reg 5] =
            some [framePtr + regB * L, calleeFrame + idx * L, L] :=
          evalArgs_cons hsrc_eval (evalArgs_cons hdst_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
        have hsrc_end : framePtr + regB * L + L < 2 ^ w := by
          have := slot_end_le_frame (by omega : regB < slots) (L := L); omega
        have hdst_end : calleeFrame + idx * L + L < 2 ^ w := by
          have := slot_end_le_frame (by simp at hid; omega : idx < slots) (L := L); omega
        have hsrc_lt_dst : framePtr + regB * L + L ≤ calleeFrame + idx * L := by
          have := slot_end_le_frame (by omega : regB < slots) (L := L); omega
        have hpre_cp : (mwCopyContract w).pre [framePtr + regB * L, calleeFrame + idx * L, L] st₁.mem :=
          ⟨framePtr + regB * L, calleeFrame + idx * L, L, rfl, hw1, hsrc_end, hdst_end,
            Or.inr (Or.inl hsrc_lt_dst)⟩
        obtain ⟨st₂, c₂, _, hcall, hpost₂, _, hother₂, hc₂⟩ :=
          runs_call_of_meetsContract (r := 8) (mwCopy_of_arithModule hArith) hargs_cp
            (by
              intro a ha
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl | rfl <;> omega)
            hpre_cp ω
        rcases hpost₂ with ⟨_, _, _, heq₂, _, hcp₂, hfr₂⟩
        simp only [List.cons.injEq, and_true] at heq₂
        rcases heq₂ with ⟨rfl, rfl, rfl⟩
        have hfr_scratch₁ : ∀ q, q < framePtr + regB * L ∨ framePtr + slots * L ≤ q →
            st₁.mem q = st.mem q := by
          intro q hq
          rcases hq with hlt | hge
          · exact hfr₁ q (Or.inl hlt) (Or.inl (by
              have := slot_mul_le_mul (by omega : regB ≤ regB + 1) (L := L); omega))
          · have h1 : framePtr + regB * L + L ≤ framePtr + slots * L := by
              have := slot_end_le_frame (by omega : regB < slots) (L := L); omega
            have h2 : framePtr + (regB + 1 + exprTempDepth e) * L ≤ framePtr + slots * L := by
              have := slot_mul_le_mul he_ts (L := L); omega
            exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
        have hfr_slots₂ : ∀ q, (q < framePtr + regB * L ∨ framePtr + slots * L ≤ q) →
            (q < calleeFrame + idx * L ∨ calleeFrame + (idx + 1) * L ≤ q) →
            st₂.mem q = st.mem q := by
          intro q hqf hqc
          have hqc' : q < calleeFrame + idx * L ∨ calleeFrame + idx * L + L ≤ q := by
            rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at hqc; exact hqc
          rw [hfr₂ q hqc', hfr_scratch₁ q hqf]
        have r2_2 : st₂.regs 2 = framePtr := by rw [hother₂ 2 (by omega), r2_1]
        have r3_2 : st₂.regs 3 = ctrl := by rw [hother₂ 3 (by omega), r3_1]
        have r5_2 : st₂.regs 5 = L := by rw [hother₂ 5 (by omega), r5_1]
        have r6_2 : st₂.regs 6 = h := by rw [hother₂ 6 (by omega), r6_1]
        have r7_2 : st₂.regs 7 = 2 ^ h := by rw [hother₂ 7 (by omega), r7_1]
        have hrC_2 : st₂.regs rCallee = calleeFrame := by rw [hother₂ rCallee hrC8, hrC_1]
        have hm2_ctrl : st₂.mem ctrl = root := by
          rw [hfr_slots₂ ctrl (Or.inl (by omega)) (Or.inl (by omega)), hm_ctrl]
        have hfr_inTrie₂ : ∀ q, InTrie st.mem L h L root q → st₂.mem q = st.mem q := by
          intro q hq
          refine hfr_slots₂ q ?_ ?_
          · rcases (htrie_disj q hq).1 with hlt | hge
            · exact Or.inl (by omega)
            · exact Or.inr hge
          · rcases (htrie_disj q hq).2 with hlt | hge
            · exact Or.inl (by omega)
            · exact Or.inr (by
                have := slot_mul_le_mul (by simp at hid; omega : idx + 1 ≤ slots) (L := L); omega)
        have hsub₂ : Subtrie st₂.mem L h hp L root gst.mem :=
          subtrie_congr_mem hfr_inTrie₂ hsub
        have htrie_disj₂ : ∀ q, InTrie st₂.mem L h L root q →
            (q < framePtr ∨ framePtr + slots * L ≤ q) ∧
            (q < calleeFrame ∨ calleeFrame + slots * L ≤ q) := by
          intro q hq
          rw [inTrie_congr_mem L root hfr_inTrie₂ q] at hq
          exact htrie_disj q hq
        have hreg_lim₂ : ∀ r < regB, LimbsAt st₂.mem (framePtr + r * L) L h (gst.regs r) := by
          intro r hr
          refine (hreg_lim r hr).congr fun q hq1 hq2 => ?_
          have h1 : r * L + L ≤ regB * L := slot_end_le_frame hr
          exact hfr_slots₂ q (Or.inl (by omega)) (Or.inl (by omega))
        obtain ⟨st₃, c₃, hr₃, hreg₃, hlim₃, hfr₃, hc₃⟩ :=
          ih (idx + 1) vs' st₂ gst hes_v hes_rb hes_ts (by simp at hid; omega)
            r2_2 r3_2 r5_2 r6_2 r7_2 hrC_2 hm2_ctrl hsub₂ htrie_disj₂ hreg_lt hreg_lim₂ hmem_lt
        have hr_comb : Runs w p ω (compileCallArgs arithBase trieBase regB rCallee idx (e :: es))
            st .normal st₃ (c₁ + (c₂ + c₃ + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + c₃ + 1, hr₁,
            runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃, hcall, hr₃, rfl⟩), rfl⟩)
        refine ⟨st₃, _, hr_comb,
          fun r hr => (hreg₃ r hr).trans ((hother₂ r hr).trans (hreg₁ r hr)),
          fun k hk => ?_, fun q hqf hqc => ?_, ?_⟩
        · cases k with
          | zero =>
            simp only [Nat.add_zero, List.getElem_cons_zero]
            refine limbsAt_iff_pointwise.mpr ⟨hv_lh, fun m hm => ?_⟩
            have hm_outside_f : calleeFrame + idx * L + m < framePtr + regB * L ∨
                framePtr + slots * L ≤ calleeFrame + idx * L + m :=
              Or.inr (by have := slot_end_le_frame (by omega : regB < slots) (L := L); omega)
            have hm_outside_c : calleeFrame + idx * L + m < calleeFrame + (idx + 1) * L ∨
                calleeFrame + (idx + 1 + es.length) * L ≤ calleeFrame + idx * L + m :=
              Or.inl (by rw [Nat.add_mul, Nat.one_mul]; omega)
            rw [hfr₃ (calleeFrame + idx * L + m) hm_outside_f hm_outside_c, hcp₂ m hm]
            exact hlim₁.getElem hm
          | succ k' =>
            simp only [List.length_cons, List.getElem_cons_succ] at hk ⊢
            rw [show idx + (k' + 1) = idx + 1 + k' by omega]
            exact hlim₃ k' (Nat.lt_of_succ_lt_succ hk)
        · have hqc1 : q < calleeFrame + idx * L ∨ calleeFrame + (idx + 1) * L ≤ q := by
            rcases hqc with hlt | hge
            · exact Or.inl hlt
            · simp only [List.length_cons] at hge
              have := slot_mul_le_mul (by omega : idx + 1 ≤ idx + (es.length + 1)) (L := L)
              exact Or.inr (by omega)
          have hqc2 : q < calleeFrame + (idx + 1) * L ∨ calleeFrame + (idx + 1 + es.length) * L ≤ q := by
            rcases hqc with hlt | hge
            · have := slot_mul_le_mul (by omega : idx ≤ idx + 1) (L := L)
              exact Or.inl (by omega)
            · simp only [List.length_cons] at hge
              exact Or.inr (by rw [show idx + 1 + es.length = idx + (es.length + 1) by omega]; exact hge)
          rw [hfr₃ q hqf hqc2, hfr_slots₂ q hqf hqc1]
        · dsimp only [mwCopyContract] at hc₂
          simp only [slotAddr, Expr.size, argsSize] at hc₂ ⊢
          have hLw' : L ≤ L * w' := Nat.le_mul_of_pos_right _ hw'1
          have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
          have h1e : 1 ≤ e.size := by cases e <;> simp [Expr.size]
          have h17 : 17 * L ≤ 17 * (L * w') := Nat.mul_le_mul_left 17 hLw'
          have h25 : 25 ≤ 25 * (L * w') := Nat.le_mul_of_pos_right 25 h1w'
          have h50 : 17 * L + 25 ≤ 50 * (L * w') := by omega
          have h50_e : 50 * (L * w') ≤ 50 * (L * w') * e.size := Nat.le_mul_of_pos_right _ h1e
          have h50' : 50 * (L * w') * e.size = 50 * L * w' * e.size := by ring
          have h800_50 : 800 * L * w' * e.size + 50 * L * w' * e.size = 850 * L * w' * e.size := by ring
          have hdist : 850 * L * w' * (e.size + argsSize es) =
              850 * L * w' * e.size + 850 * L * w' * argsSize es := by ring
          omega

end MinCostFlow.WideWord
