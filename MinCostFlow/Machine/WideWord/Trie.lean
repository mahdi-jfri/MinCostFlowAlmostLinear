module

public import WordRAM.Logic
public import WordRAM.Tactic
public import WordRAM.Layout
public import MinCostFlow.Machine.WideWord.ArithMulDiv

/-!
# Lazy trie for wide-word guest memory

This file implements a lazy `2 ^ h`-ary trie of depth `L` representing an `ℕ → ℕ` guest memory
whose keys `< 2 ^ (L * h)` and values `< 2 ^ (L * h)` are encoded as `L`-limb `h`-bit words:
* `InTrie mem L h d root p`: whether host address `p` belongs to the trie rooted at `root`.
* `Subtrie mem L h hp d root f`: inductive representation predicate ensuring non-null subtrees lie
  in `[1, hp)`, children do not overlap parents, and siblings are pairwise disjoint.
* `TrieRep mem L h hp root f`: top-level invariant bundling `1 ≤ hp`, `Subtrie mem L h hp L root f`,
  and `ZeroFrom mem hp`.
* `trieRead` and `trieWrite` in `O(L)` host time; `trieWrite` consumes `≤ L * 2 ^ h + L` bump words.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Module indices -/

def idxTrieRead : ℕ := 0
def idxTrieWrite : ℕ := 1

/-! ### Lazy trie footprint and representation -/

/-- Host addresses belonging to the subtrie of depth `d` rooted at `root` (with `0` null). -/
def InTrie (mem : ℕ → ℕ) (L h : ℕ) : ℕ → ℕ → ℕ → Prop
  | _, 0, _ => False
  | 0, root, p => root ≤ p ∧ p < root + L
  | d + 1, root, p =>
      (root ≤ p ∧ p < root + 2 ^ h) ∨
      ∃ k < 2 ^ h, InTrie mem L h d (mem (root + k)) p

theorem inTrie_zero_root (mem : ℕ → ℕ) (L h d p : ℕ) : ¬ InTrie mem L h d 0 p := by
  cases d <;> simp [InTrie]

theorem inTrie_leaf_iff {mem : ℕ → ℕ} {L h root p : ℕ} (hr : root ≠ 0) :
    InTrie mem L h 0 root p ↔ root ≤ p ∧ p < root + L := by
  cases root with
  | zero => contradiction
  | succ r => rfl

theorem inTrie_node_iff {mem : ℕ → ℕ} {L h d root p : ℕ} (hr : root ≠ 0) :
    InTrie mem L h (d + 1) root p ↔
      (root ≤ p ∧ p < root + 2 ^ h) ∨
      ∃ k < 2 ^ h, InTrie mem L h d (mem (root + k)) p := by
  cases root with
  | zero => contradiction
  | succ r => rfl

theorem inTrie_congr_mem {mem mem' : ℕ → ℕ} {L h : ℕ} :
    ∀ (d root : ℕ), (∀ q, InTrie mem L h d root q → mem' q = mem q) →
      ∀ p, InTrie mem' L h d root p ↔ InTrie mem L h d root p := by
  intro d
  induction d with
  | zero =>
    intro root _ p
    by_cases hr : root = 0
    · subst hr; simp [inTrie_zero_root]
    · simp [inTrie_leaf_iff hr]
  | succ d ih =>
    intro root hmem p
    by_cases hr : root = 0
    · subst hr; simp [inTrie_zero_root]
    · simp only [inTrie_node_iff hr]
      constructor
      · rintro (hp | ⟨k, hk, hch⟩)
        · exact Or.inl hp
        · have hmk : mem' (root + k) = mem (root + k) :=
            hmem (root + k) ((inTrie_node_iff hr).mpr (Or.inl ⟨by omega,
              Nat.add_lt_add_left hk _⟩))
          rw [hmk] at hch
          have ihk := ih (mem (root + k)) (fun q hq =>
            hmem q ((inTrie_node_iff hr).mpr (Or.inr ⟨k, hk, hq⟩))) p
          exact Or.inr ⟨k, hk, ihk.mp hch⟩
      · rintro (hp | ⟨k, hk, hch⟩)
        · exact Or.inl hp
        · have hmk : mem' (root + k) = mem (root + k) :=
            hmem (root + k) ((inTrie_node_iff hr).mpr (Or.inl ⟨by omega,
              Nat.add_lt_add_left hk _⟩))
          have ihk := ih (mem (root + k)) (fun q hq =>
            hmem q ((inTrie_node_iff hr).mpr (Or.inr ⟨k, hk, hq⟩))) p
          exact Or.inr ⟨k, hk, by rw [hmk]; exact ihk.mpr hch⟩

/-- `Subtrie mem L h hp d root f`: `root` (with `0` representing the zero map) represents `f`
on keys `< 2 ^ (d * h)` using host addresses in `[1, hp)` with no parent-child or sibling
overlap. Keys are decomposed least-significant limb first (`k + 2 ^ h * q`). -/
def Subtrie (mem : ℕ → ℕ) (L h hp : ℕ) : ℕ → ℕ → (ℕ → ℕ) → Prop
  | 0, root, f =>
      if root = 0 then f 0 = 0
      else 1 ≤ root ∧ root + L ≤ hp ∧ LimbsAt mem root L h (f 0)
  | d + 1, root, f =>
      if root = 0 then ∀ q < 2 ^ ((d + 1) * h), f q = 0
      else
        1 ≤ root ∧ root + 2 ^ h ≤ hp ∧
        (∀ k < 2 ^ h, Subtrie mem L h hp d (mem (root + k)) (fun q => f (k + 2 ^ h * q))) ∧
        (∀ k < 2 ^ h, ∀ p, InTrie mem L h d (mem (root + k)) p →
          ¬ (root ≤ p ∧ p < root + 2 ^ h)) ∧
        (∀ k₁ k₂, k₁ < 2 ^ h → k₂ < 2 ^ h → k₁ ≠ k₂ → ∀ p,
          InTrie mem L h d (mem (root + k₁)) p → ¬ InTrie mem L h d (mem (root + k₂)) p)

theorem inTrie_bounds {mem : ℕ → ℕ} {L h hp : ℕ} :
    ∀ {d root : ℕ} {f : ℕ → ℕ}, Subtrie mem L h hp d root f →
      ∀ p, InTrie mem L h d root p → 1 ≤ p ∧ p < hp := by
  intro d
  induction d with
  | zero =>
    intro root f hsub p hp_in
    by_cases hr : root = 0
    · subst hr; exact False.elim (inTrie_zero_root _ _ _ _ _ hp_in)
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      rw [inTrie_leaf_iff hr] at hp_in
      omega
  | succ d ih =>
    intro root f hsub p hp_in
    by_cases hr : root = 0
    · subst hr; exact False.elim (inTrie_zero_root _ _ _ _ _ hp_in)
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      rcases hsub with ⟨hr1, hrhp, hch, _, _⟩
      rw [inTrie_node_iff hr] at hp_in
      rcases hp_in with ⟨hp1, hp2⟩ | ⟨k, hk, hkin⟩
      · omega
      · exact ih (hch k hk) p hkin

theorem subtrie_root_lt {mem : ℕ → ℕ} {w L h hp d root : ℕ} {f : ℕ → ℕ}
    (hsub : Subtrie mem L h hp d root f) (hhp : hp < 2 ^ w) (hw : 1 < 2 ^ w) :
    root < 2 ^ w := by
  by_cases hr : root = 0
  · subst hr; omega
  · cases d with
    | zero =>
      simp only [Subtrie, hr, ↓reduceIte] at hsub
      omega
    | succ d =>
      simp only [Subtrie, hr, ↓reduceIte] at hsub
      have hle : root ≤ hp := Nat.le_trans (Nat.le_add_right root (2 ^ h)) hsub.2.1
      omega

theorem subtrie_mono_hp {mem : ℕ → ℕ} {L h hp hp' : ℕ} (hle : hp ≤ hp') :
    ∀ {d root : ℕ} {f : ℕ → ℕ}, Subtrie mem L h hp d root f → Subtrie mem L h hp' d root f := by
  intro d
  induction d with
  | zero =>
    intro root f hsub
    by_cases hr : root = 0
    · simpa [Subtrie, hr] using hsub
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      exact ⟨hsub.1, le_trans hsub.2.1 hle, hsub.2.2⟩
  | succ d ih =>
    intro root f hsub
    by_cases hr : root = 0
    · simpa [Subtrie, hr] using hsub
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      rcases hsub with ⟨hr1, hrhp, hch, hdisj, hsib⟩
      exact ⟨hr1, le_trans hrhp hle, fun k hk => ih (hch k hk), hdisj, hsib⟩

theorem subtrie_congr_func {mem : ℕ → ℕ} {L h hp : ℕ} :
    ∀ {d root : ℕ} {f g : ℕ → ℕ}, (∀ q < 2 ^ (d * h), f q = g q) →
      (Subtrie mem L h hp d root f → Subtrie mem L h hp d root g) := by
  intro d
  induction d with
  | zero =>
    intro root f g hfg hsub
    have h0 : f 0 = g 0 := hfg 0 (by simp)
    by_cases hr : root = 0 <;> simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
    · rw [← h0]; exact hsub
    · rw [← h0]; exact hsub
  | succ d ih =>
    intro root f g hfg hsub
    by_cases hr : root = 0
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      intro q hq; rw [← hfg q hq]; exact hsub q hq
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      rcases hsub with ⟨hr1, hrhp, hch, hdisj, hsib⟩
      refine ⟨hr1, hrhp, fun k hk => ih (fun q hq => hfg (k + 2 ^ h * q) ?_) (hch k hk),
        hdisj, hsib⟩
      have hmul : 2 ^ ((d + 1) * h) = 2 ^ h * 2 ^ (d * h) := by
        rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hmul]
      have hle1 : 2 ^ h * (q + 1) ≤ 2 ^ h * 2 ^ (d * h) := Nat.mul_le_mul_left _ hq
      rw [Nat.mul_add, Nat.mul_one] at hle1
      omega

theorem subtrie_ext {mem : ℕ → ℕ} {L h hp : ℕ} :
    ∀ {d root : ℕ} {f₁ f₂ : ℕ → ℕ},
      Subtrie mem L h hp d root f₁ → Subtrie mem L h hp d root f₂ →
      ∀ q < 2 ^ (d * h), f₁ q = f₂ q := by
  intro d
  induction d with
  | zero =>
    intro root f₁ f₂ h1 h2 q hq
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    by_cases hr : root = 0
    · simp only [Subtrie, hr, ↓reduceIte] at h1 h2
      rw [h1, h2]
    · simp only [Subtrie, hr, ↓reduceIte] at h1 h2
      exact h1.2.2.ext h2.2.2
  | succ d ih =>
    intro root f₁ f₂ h1 h2 q hq
    by_cases hr : root = 0
    · simp only [Subtrie, hr, ↓reduceIte] at h1 h2
      rw [h1 q hq, h2 q hq]
    · simp only [Subtrie, hr, ↓reduceIte] at h1 h2
      rcases h1 with ⟨_, _, hch1, _, _⟩
      rcases h2 with ⟨_, _, hch2, _, _⟩
      have hqm : q % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hqd : q / 2 ^ h < 2 ^ (d * h) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc q < 2 ^ ((d + 1) * h) := hq
          _ = 2 ^ (d * h) * 2 ^ h := by rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul]
      have hstep := ih (hch1 (q % 2 ^ h) hqm) (hch2 (q % 2 ^ h) hqm) (q / 2 ^ h) hqd
      rwa [Nat.mod_add_div] at hstep

theorem subtrie_congr_mem {mem mem' : ℕ → ℕ} {L h hp : ℕ} :
    ∀ {d root : ℕ} {f : ℕ → ℕ}, (∀ q, InTrie mem L h d root q → mem' q = mem q) →
      Subtrie mem L h hp d root f → Subtrie mem' L h hp d root f := by
  intro d
  induction d with
  | zero =>
    intro root f hmem hsub
    by_cases hr : root = 0
    · simpa [Subtrie, hr] using hsub
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      refine ⟨hsub.1, hsub.2.1, hsub.2.2.congr fun q hq1 hq2 => ?_⟩
      exact hmem q ((inTrie_leaf_iff hr).mpr ⟨hq1, hq2⟩)
  | succ d ih =>
    intro root f hmem hsub
    by_cases hr : root = 0
    · simpa [Subtrie, hr] using hsub
    · simp only [Subtrie, hr, ↓reduceIte] at hsub ⊢
      rcases hsub with ⟨hr1, hrhp, hch, hdisj, hsib⟩
      have hmk : ∀ k < 2 ^ h, mem' (root + k) = mem (root + k) := fun k hk =>
        hmem (root + k) ((inTrie_node_iff hr).mpr (Or.inl ⟨by omega, Nat.add_lt_add_left hk _⟩))
      have hin_eq : ∀ k < 2 ^ h, ∀ p,
          InTrie mem' L h d (mem' (root + k)) p ↔ InTrie mem L h d (mem (root + k)) p := by
        intro k hk p
        rw [hmk k hk]
        exact inTrie_congr_mem d (mem (root + k)) (fun q hq =>
          hmem q ((inTrie_node_iff hr).mpr (Or.inr ⟨k, hk, hq⟩))) p
      refine ⟨hr1, hrhp, ?_, ?_, ?_⟩
      · intro k hk
        rw [hmk k hk]
        exact ih (fun q hq => hmem q ((inTrie_node_iff hr).mpr (Or.inr ⟨k, hk, hq⟩))) (hch k hk)
      · intro k hk p hp
        rw [hin_eq k hk p] at hp
        exact hdisj k hk p hp
      · intro k₁ k₂ hk₁ hk₂ hne p hp1 hp2
        rw [hin_eq k₁ hk₁ p] at hp1
        rw [hin_eq k₂ hk₂ p] at hp2
        exact hsib k₁ k₂ hk₁ hk₂ hne p hp1 hp2

theorem subtrie_lt_pow {mem : ℕ → ℕ} {L h hp : ℕ} :
    ∀ {d root : ℕ} {f : ℕ → ℕ}, Subtrie mem L h hp d root f →
      ∀ q < 2 ^ (d * h), f q < 2 ^ (L * h) := by
  intro d
  induction d with
  | zero =>
    intro root f hsub q hq
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    by_cases hr : root = 0
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      rw [hsub]; exact Nat.two_pow_pos _
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      exact hsub.2.2.lt_pow
  | succ d ih =>
    intro root f hsub q hq
    by_cases hr : root = 0
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      rw [hsub q hq]; exact Nat.two_pow_pos _
    · simp only [Subtrie, hr, ↓reduceIte] at hsub
      rcases hsub with ⟨_, _, hch, _, _⟩
      have hqm : q % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hqd : q / 2 ^ h < 2 ^ (d * h) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc q < 2 ^ ((d + 1) * h) := hq
          _ = 2 ^ (d * h) * 2 ^ h := by rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul]
      have hstep := ih (hch (q % 2 ^ h) hqm) (q / 2 ^ h) hqd
      rwa [Nat.mod_add_div] at hstep

/-- Top-level lazy trie invariant: `root` represents `f : ℕ → ℕ` using memory in `[1, hp)`
with `ZeroFrom mem hp`. -/
def TrieRep (mem : ℕ → ℕ) (L h hp root : ℕ) (f : ℕ → ℕ) : Prop :=
  1 ≤ hp ∧ Subtrie mem L h hp L root f ∧ ZeroFrom mem hp

theorem trieRep_mono_hp {mem : ℕ → ℕ} {L h hp hp' root : ℕ} {f : ℕ → ℕ}
    (ht : TrieRep mem L h hp root f) (hle : hp ≤ hp') (hz : ZeroFrom mem hp') :
    TrieRep mem L h hp' root f :=
  ⟨le_trans ht.1 hle, subtrie_mono_hp hle ht.2.1, hz⟩

theorem trieRep_congr_mem {mem mem' : ℕ → ℕ} {L h hp root : ℕ} {f : ℕ → ℕ}
    (ht : TrieRep mem L h hp root f)
    (hin : ∀ p, InTrie mem L h L root p → mem' p = mem p)
    (hz : ZeroFrom mem' hp) :
    TrieRep mem' L h hp root f :=
  ⟨ht.1, subtrie_congr_mem hin ht.2.1, hz⟩

/-! ### Key-splitting and deterministic walk helpers -/

private theorem key_split_step (addr i h q : ℕ) :
    addr % 2 ^ (i * h) + 2 ^ (i * h) * ((addr / 2 ^ (i * h)) % 2 ^ h + 2 ^ h * q) =
      addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q := by
  have h1 : addr % (2 ^ (i * h) * 2 ^ h) =
      addr % 2 ^ (i * h) + 2 ^ (i * h) * ((addr / 2 ^ (i * h)) % 2 ^ h) := by
    have hsplit := Nat.mod_add_div (addr % (2 ^ (i * h) * 2 ^ h)) (2 ^ (i * h))
    rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at hsplit
    exact hsplit.symm
  have hexp : (i + 1) * h = i * h + h := by ring
  rw [hexp, Nat.pow_add, h1]
  ring

private theorem key_decompose_iff {k q rest B : ℕ} (hk : k < B) :
    k + B * q = rest ↔ k = rest % B ∧ q = rest / B := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hk, Nat.zero_add]
  · rintro ⟨rfl, rfl⟩
    exact Nat.mod_add_div rest B

private theorem div_mul_pow_step (addr i h : ℕ) :
    (addr / 2 ^ (i * h)) / 2 ^ h = addr / 2 ^ ((i + 1) * h) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show i * h + h = (i + 1) * h by ring]

private theorem disjoint_range_of_inTrie {S : ℕ → Prop} {a b L : ℕ}
    (ha : ∀ i < L, S (a + i)) (hb : ∀ i < L, ¬ S (b + i)) :
    a + L ≤ b ∨ b + L ≤ a := by
  by_cases hL0 : L = 0
  · subst hL0; omega
  · by_contra hnot
    have hlt1 : a < b + L := by omega
    have hlt2 : b < a + L := by omega
    have hm_ge_a : a ≤ max a b := le_max_left _ _
    have hm_ge_b : b ≤ max a b := le_max_right _ _
    have hm_lt_a : max a b < a + L := max_lt (by omega) hlt2
    have hm_lt_b : max a b < b + L := max_lt hlt1 (by omega)
    have h1 := ha (max a b - a) (by omega)
    have h2 := hb (max a b - b) (by omega)
    rw [show a + (max a b - a) = max a b by omega] at h1
    rw [show b + (max a b - b) = max a b by omega] at h2
    exact h2 h1

/-- Pure lookup of the leaf pointer along `d` digits stored at `mem[addrPtr + i .. addrPtr + i + d - 1]`. -/
private def trieLookupPtr (mem : ℕ → ℕ) (addrPtr : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, cur => cur
  | _ + 1, _, 0 => 0
  | d + 1, i, cur => trieLookupPtr mem addrPtr d (i + 1) (mem (cur + mem (addrPtr + i)))

private theorem subtrie_trieLookupPtr {mem : ℕ → ℕ} {addrPtr L h hp : ℕ} :
    ∀ (d i cur : ℕ) {f : ℕ → ℕ} (addr : ℕ),
      i + d = L →
      Subtrie mem L h hp d cur (fun q => f (addr % 2 ^ (i * h) + 2 ^ (i * h) * q)) →
      LimbsAt mem addrPtr L h addr →
      Subtrie mem L h hp 0 (trieLookupPtr mem addrPtr d i cur) (fun q => f (addr + 2 ^ (L * h) * q)) ∧
        (∀ q, InTrie mem L h 0 (trieLookupPtr mem addrPtr d i cur) q → InTrie mem L h d cur q) := by
  intro d
  induction d with
  | zero =>
    intro i cur f addr hid hsub haddr
    have hiL : i = L := by omega
    subst hiL
    have hmod : addr % 2 ^ (i * h) = addr := Nat.mod_eq_of_lt haddr.lt_pow
    simp only [hmod] at hsub
    simp only [trieLookupPtr]
    exact ⟨hsub, fun q hq => hq⟩
  | succ d ih =>
    intro i cur f addr hid hsub haddr
    have hiL : i < L := by omega
    set dig := (addr / 2 ^ (i * h)) % 2 ^ h
    have hdig_lt : dig < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hdig_mem : mem (addrPtr + i) = dig := haddr.getElem hiL
    by_cases hcur0 : cur = 0
    · subst hcur0
      simp only [Subtrie, ↓reduceIte] at hsub
      have hzero_rem : ∀ q < 2 ^ (d * h),
          f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q) = 0 := by
        intro q hq
        have hsum_lt : dig + 2 ^ h * q < 2 ^ ((d + 1) * h) := by
          have hmul : 2 ^ ((d + 1) * h) = 2 ^ h * 2 ^ (d * h) := by
            rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hmul]
          have hle1 : 2 ^ h * (q + 1) ≤ 2 ^ h * 2 ^ (d * h) := Nat.mul_le_mul_left _ hq
          rw [Nat.mul_add, Nat.mul_one] at hle1
          omega
        have := hsub (dig + 2 ^ h * q) hsum_lt
        simpa [dig, key_split_step] using this
      have hsub_zero : Subtrie mem L h hp d 0
          (fun q => f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
        cases d with
        | zero => simpa [Subtrie] using hzero_rem 0 (by simp)
        | succ d' => simpa [Subtrie] using hzero_rem
      have hrec := ih (i + 1) 0 addr (by omega) hsub_zero haddr
      have hptr0 : trieLookupPtr mem addrPtr (d + 1) i 0 = 0 := by
        simp [trieLookupPtr]
      have hptr0' : trieLookupPtr mem addrPtr d (i + 1) 0 = 0 := by
        cases d <;> simp [trieLookupPtr]
      rw [hptr0]
      rw [hptr0'] at hrec
      refine ⟨hrec.1, fun q hq => False.elim (inTrie_zero_root _ _ _ _ _ hq)⟩
    · simp only [Subtrie, hcur0, ↓reduceIte] at hsub
      rcases hsub with ⟨hcur1, hcur_hp, hch, _, _⟩
      have hsub_next : Subtrie mem L h hp d (mem (cur + dig))
          (fun q => f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
        have hc := hch dig hdig_lt
        simpa [dig, key_split_step] using hc
      have hrec := ih (i + 1) (mem (cur + dig)) addr (by omega) hsub_next haddr
      have hptr_eq : trieLookupPtr mem addrPtr (d + 1) i cur =
          trieLookupPtr mem addrPtr d (i + 1) (mem (cur + dig)) := by
        cases cur with
        | zero => contradiction
        | succ c => simp only [trieLookupPtr, hdig_mem]
      rw [hptr_eq]
      refine ⟨hrec.1, fun q hq => ?_⟩
      exact (inTrie_node_iff hcur0).mpr (Or.inr ⟨dig, hdig_lt, hrec.2 q hq⟩)

/-! ### Trie procedures and contracts -/

/-- Reads `f addr` (`L`-limb `h`-bit word) from trie `root` at `[addrPtr]` into `[dstPtr]`.
Args: `[root, addrPtr, dstPtr, L]`. Returns `0`. Cost: `≤ 40 * L + 35`. -/
def trieRead (arithBase : ℕ) : Stmt :=
  .assign 5 (.reg 0) ;;
  forRange 6 (.const 0) (.reg 3)
    (.cond (.reg 5)
      (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
       .assign 5 (.load (.bin .add (.reg 5) (.reg 7))))
      .nop) ;;
  .cond (.reg 5)
    (.call 7 (arithBase + idxCopy) [.reg 5, .reg 2, .reg 3])
    (.call 7 (arithBase + idxZero) [.reg 2, .reg 3]) ;;
  .ret (.const 0)

/-- Writes `val` (`valPtr`) at key `addr` (`addrPtr`) into the trie whose root lives at `rootPtr`
and bump pointer lives at `hpPtr`. Args: `[rootPtr, hpPtr, addrPtr, valPtr, L, 2 ^ h]`. Returns `0`.
Cost: `≤ 60 * L + 50`; allocates `≤ L * 2 ^ h + L` words. -/
def trieWrite (arithBase : ℕ) : Stmt :=
  .assign 6 (.reg 0) ;;
  forRange 7 (.const 0) (.reg 4)
    (.assign 8 (.load (.reg 6)) ;;
     .cond (.reg 8) .nop
       (.assign 8 (.load (.reg 1)) ;;
        .store (.reg 1) (.bin .add (.reg 8) (.reg 5)) ;;
        .store (.reg 6) (.reg 8)) ;;
     .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
     .assign 6 (.bin .add (.reg 8) (.reg 9))) ;;
  .assign 9 (.load (.reg 6)) ;;
  .cond (.reg 9) .nop
    (.assign 9 (.load (.reg 1)) ;;
     .store (.reg 1) (.bin .add (.reg 9) (.reg 4)) ;;
     .store (.reg 6) (.reg 9)) ;;
  .call 8 (arithBase + idxCopy) [.reg 3, .reg 9, .reg 4] ;;
  .ret (.const 0)

def trieModule (arithBase : ℕ) : List Stmt :=
  [trieRead arithBase, trieWrite arithBase]

theorem trieModule_length (arithBase : ℕ) : (trieModule arithBase).length = 2 := rfl

theorem trieRead_noRand (arithBase : ℕ) : (trieRead arithBase).NoRand := by
  simp [trieRead, forRange, forUp, Stmt.NoRand]

theorem trieWrite_noRand (arithBase : ℕ) : (trieWrite arithBase).NoRand := by
  simp [trieWrite, forRange, forUp, Stmt.NoRand]

theorem trieModule_noRand (arithBase : ℕ) : ∀ s ∈ trieModule arithBase, s.NoRand := by
  intro s hs
  simp only [trieModule, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact trieRead_noRand _
  · exact trieWrite_noRand _

def trieReadContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ root addrPtr dstPtr L h hp f addr, args = [root, addrPtr, dstPtr, L] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ hp < 2 ^ w ∧ addrPtr + L < 2 ^ w ∧ dstPtr + L < 2 ^ w ∧
      (∀ p, InTrie mem L h L root p → p < dstPtr ∨ dstPtr + L ≤ p) ∧
      Subtrie mem L h hp L root f ∧ LimbsAt mem addrPtr L h addr
  post args mem v mem' :=
    ∃ root addrPtr dstPtr L, args = [root, addrPtr, dstPtr, L] ∧ v = 0 ∧
      (∀ h hp f addr, Subtrie mem L h hp L root f → LimbsAt mem addrPtr L h addr →
        LimbsAt mem' dstPtr L h (f addr)) ∧
      (∀ p, p < dstPtr ∨ dstPtr + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L] => 40 * L + 35 | _ => 0

def trieWriteContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ rootPtr hpPtr addrPtr valPtr L h root hp f addr val,
      args = [rootPtr, hpPtr, addrPtr, valPtr, L, 2 ^ h] ∧
      1 ≤ L ∧ 1 ≤ h ∧ 2 * h + 2 ≤ w ∧
      1 ≤ hp ∧ mem rootPtr = root ∧ mem hpPtr = hp ∧
      Subtrie mem L h hp L root f ∧ ZeroFrom mem hp ∧
      hp + L * 2 ^ h + L < 2 ^ w ∧
      rootPtr < hp ∧ hpPtr < hp ∧ rootPtr ≠ hpPtr ∧
      ¬ InTrie mem L h L root rootPtr ∧ ¬ InTrie mem L h L root hpPtr ∧
      addrPtr + L ≤ hp ∧ valPtr + L ≤ hp ∧
      (∀ i < L, addrPtr + i ≠ rootPtr ∧ addrPtr + i ≠ hpPtr ∧ ¬ InTrie mem L h L root (addrPtr + i)) ∧
      (∀ i < L, valPtr + i ≠ rootPtr ∧ valPtr + i ≠ hpPtr ∧ ¬ InTrie mem L h L root (valPtr + i)) ∧
      LimbsAt mem addrPtr L h addr ∧ LimbsAt mem valPtr L h val
  post args mem v mem' :=
    ∃ rootPtr hpPtr addrPtr valPtr L B,
      args = [rootPtr, hpPtr, addrPtr, valPtr, L, B] ∧ v = 0 ∧
      mem hpPtr ≤ mem' hpPtr ∧ mem' hpPtr ≤ mem hpPtr + L * B + L ∧
      (∀ h f addr val, B = 2 ^ h → Subtrie mem L h (mem hpPtr) L (mem rootPtr) f →
        LimbsAt mem addrPtr L h addr → LimbsAt mem valPtr L h val →
        Subtrie mem' L h (mem' hpPtr) L (mem' rootPtr) (Function.update f addr val) ∧
        (∀ p, InTrie mem' L h L (mem' rootPtr) p →
          InTrie mem L h L (mem rootPtr) p ∨ (mem hpPtr ≤ p ∧ p < mem' hpPtr))) ∧
      ZeroFrom mem' (mem' hpPtr) ∧
      (∀ h p, B = 2 ^ h → p ≠ rootPtr → p ≠ hpPtr →
        ¬ InTrie mem L h L (mem rootPtr) p → p < mem hpPtr → mem' p = mem p)
  cost args _ := match args with | [_, _, _, _, L, _] => 60 * L + 50 | _ => 0

/-! ### Verification of `trieRead` -/

theorem trieRead_meetsContract {w : ℕ} {p : Program} {fProc arithBase : ℕ}
    (hZero : MeetsContract w p (arithBase + idxZero) (mwZeroContract w))
    (hCopy : MeetsContract w p (arithBase + idxCopy) (mwCopyContract w))
    (hProc : p.procs[fProc]? = some (trieRead arithBase)) :
    MeetsContract w p fProc (trieReadContract w) := by
  refine meetsContract_of_runs hProc ?_
  rintro args mem pos ω hwords ⟨root, addrPtr, dstPtr, L, h, hp, f, addr, rfl,
    hh, hw2, hhp_w, haddr_w, hdst_w, hdisj, hsub, haddr⟩
  have hB : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.one_le_pow h 2 (by norm_num)) hB
  have hL_w : L < 2 ^ w := by omega
  have hloop : Triple w p
      (fun st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = addrPtr ∧
        st.regs 2 = dstPtr ∧ st.regs 3 = L ∧ st.regs 5 = root)
      (forRange 6 (.const 0) (.reg 3)
        (.cond (.reg 5)
          (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
           .assign 5 (.load (.bin .add (.reg 5) (.reg 7))))
          .nop))
      (normalPost fun st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = addrPtr ∧
        st.regs 2 = dstPtr ∧ st.regs 3 = L ∧
        st.regs 5 = trieLookupPtr mem addrPtr L 0 root)
      (fun _ => (L - 0) * (14 + (Expr.reg 3).size + 8) + ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.strengthen_post (Triple.forRange_const (w := w) (p := p) (r := 6)
      (P := fun st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = addrPtr ∧
        st.regs 2 = dstPtr ∧ st.regs 3 = L ∧ st.regs 5 = root)
      (lo := .const 0) (hi := .reg 3)
      (body := .cond (.reg 5)
        (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
         .assign 5 (.load (.bin .add (.reg 5) (.reg 7))))
        .nop)
      (Inv := fun i st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = addrPtr ∧
        st.regs 2 = dstPtr ∧ st.regs 3 = L ∧ st.regs 6 = i ∧
        Subtrie mem L h hp (L - i) (st.regs 5) (fun q => f (addr % 2 ^ (i * h) + 2 ^ (i * h) * q)) ∧
        trieLookupPtr mem addrPtr (L - i) i (st.regs 5) = trieLookupPtr mem addrPtr L 0 root)
      14 0 L (Nat.zero_le L) hw1 (fun _ => hL_w)
      (fun st ⟨hm, r0, r1, r2, r3, r5⟩ => by
        refine ⟨by eval_expr, hm, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp,
          by simpa [r5, Nat.mod_one] using hsub, by simp [r5]⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.2.2.2.2.1; eval_expr)
      (fun i _ hiL => by
        intro st _ ⟨hm, r0, r1, r2, r3, r6, hsub_i, hwalk_i⟩
        set cur := st.regs 5
        have hdepth : L - i = (L - (i + 1)) + 1 := by omega
        refine runs_start_le ?_
        wram_step
        · have hcur_ne : cur ≠ 0 := hcond
          rw [hdepth] at hsub_i hwalk_i
          simp only [Subtrie, hcur_ne, ↓reduceIte] at hsub_i
          rcases hsub_i with ⟨hcur1, hcur_hp, hch, _, _⟩
          have hcur_le : cur ≤ hp := Nat.le_trans (Nat.le_add_right cur (2 ^ h)) hcur_hp
          have hcur_w : cur < 2 ^ w := by omega
          set dig := (addr / 2 ^ (i * h)) % 2 ^ h
          have hdig_lt : dig < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
          have hdig_val : st.mem (addrPtr + i) = dig := by
            rw [hm]; exact haddr.getElem hiL
          have hload_dig : (Expr.load (.bin .add (.reg 1) (.reg 6))).eval w st = some dig :=
            Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) hdig_val
          refine runs_seq_assign_le hload_dig ?_
          set next := mem (cur + dig)
          have hsub_next : Subtrie mem L h hp (L - (i + 1)) next
              (fun q => f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
            have hc := hch dig hdig_lt
            simpa [dig, key_split_step] using hc
          have hnext_w : next < 2 ^ w := subtrie_root_lt hsub_next hhp_w hw1
          have hcur_dig_w : cur + dig < 2 ^ w := by omega
          have hload_next : (Expr.load (.bin .add (.reg 5) (.reg 7))).eval w
              { mem := st.mem, regs := Function.update st.regs 7 dig, pos := st.pos } = some next :=
            Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) hcur_dig_w)
              (by rw [hm])
          refine runs_assign_le hload_next ?_ (by wram_cost)
          refine ⟨⟨hm, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp,
            by simpa using hsub_next, ?_⟩, r6⟩
          rw [← hwalk_i]
          have hst5_ne : st.regs 5 ≠ 0 := hcur_ne
          cases h5 : st.regs 5 with
          | zero => exact absurd h5 hst5_ne
          | succ c => simp [trieLookupPtr, hm ▸ hdig_val, next, cur, h5]
        · have hcur0 : cur = 0 := hcond
          refine runs_nop_le ?_ (by wram_cost)
          rw [hcur0, hdepth] at hsub_i hwalk_i
          simp only [Subtrie, ↓reduceIte] at hsub_i
          have hz_rem : ∀ q < 2 ^ ((L - (i + 1)) * h),
              f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q) = 0 := by
            intro q hq
            set dig := (addr / 2 ^ (i * h)) % 2 ^ h
            have hdig_lt : dig < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
            have hsum_lt : dig + 2 ^ h * q < 2 ^ ((L - (i + 1) + 1) * h) := by
              have hmul : 2 ^ ((L - (i + 1) + 1) * h) = 2 ^ h * 2 ^ ((L - (i + 1)) * h) := by
                rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
              rw [hmul]
              have hle1 : 2 ^ h * (q + 1) ≤ 2 ^ h * 2 ^ ((L - (i + 1)) * h) := Nat.mul_le_mul_left _ hq
              rw [Nat.mul_add, Nat.mul_one] at hle1
              omega
            have := hsub_i (dig + 2 ^ h * q) hsum_lt
            simpa [dig, key_split_step] using this
          have hsub_zero : Subtrie mem L h hp (L - (i + 1)) 0
              (fun q => f (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
            by_cases hzero : L - (i + 1) = 0
            · rw [hzero]; simpa [Subtrie] using hz_rem 0 (by simp)
            · rcases Nat.exists_eq_succ_of_ne_zero hzero with ⟨d', hd'⟩
              have hz' := hz_rem
              rw [hd'] at hz' ⊢
              simpa [Subtrie] using hz'
          have hwalk_next : trieLookupPtr mem addrPtr (L - (i + 1)) (i + 1) 0 =
              trieLookupPtr mem addrPtr L 0 root := by
            rw [← hwalk_i]
            cases hrem : L - (i + 1) with
            | zero => simp [trieLookupPtr]
            | succ d' => simp [trieLookupPtr]
          have hst5_0 : st.regs 5 = 0 := hcur0
          exact ⟨⟨hm, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp,
            by simpa [hst5_0] using hsub_zero, by simpa [hst5_0] using hwalk_next⟩, r6⟩))
      (fun o st hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨hm, r0, r1, r2, r3, _, _, hwalk⟩
          simp only [Nat.sub_self, trieLookupPtr] at hwalk
          exact ⟨hm, r0, r1, r2, r3, hwalk⟩)
  refine runs_start_le ?_
  dsimp only [trieRead]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState]⟩ ?_
  rintro st₁ ⟨hm1, r0, r1, r2, r3, hleaf_eq⟩
  set leaf := st₁.regs 5
  obtain ⟨hsub_end, hin_end⟩ := subtrie_trieLookupPtr L 0 root addr (by omega)
    (by simpa [Nat.mod_one] using hsub) haddr
  rw [← hleaf_eq] at hsub_end hin_end
  have hleaf_w : leaf < 2 ^ w := subtrie_root_lt hsub_end hhp_w hw1
  refine runs_seq_cond_le (by eval_expr)
    (fun hne_leaf => by
      have hne_leaf' : leaf ≠ 0 := by rw [hleaf_eq]; exact hne_leaf
      simp only [Subtrie, hne_leaf', ↓reduceIte] at hsub_end
      rcases hsub_end with ⟨hleaf1, hleaf_hp, hleaf_limbs⟩
      have hdisj_ld : dstPtr + L ≤ leaf ∨ leaf + L ≤ dstPtr := by
        have ha : ∀ m < L, InTrie mem L h L root (leaf + m) := fun m hm =>
          hin_end (leaf + m) ((inTrie_leaf_iff hne_leaf').mpr ⟨by omega, by omega⟩)
        rcases disjoint_range_of_inTrie ha (fun m hm => fun hin => by
          rcases hdisj (dstPtr + m) hin with hlt | hge <;> omega) with h | h
        · exact Or.inr h
        · exact Or.inl h
      refine runs_seq_call_le hCopy
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
        (by wram_words) ⟨leaf, dstPtr, L, rfl, hw1, by omega, hdst_w, Or.imp id Or.inl hdisj_ld⟩ ?_
      rintro v mem' pos' ⟨src', dst', L', heq_c, rfl, hcp_vals, hfr_cp⟩
      simp only [List.cons.injEq, and_true] at heq_c
      rcases heq_c with ⟨rfl, rfl, rfl⟩
      refine runs_ret_le (by eval_expr) ⟨root, addrPtr, dstPtr, L, rfl, rfl,
        fun h' hp' f' addr' hsub' haddr' => by
          obtain ⟨hsub'_end, _⟩ := subtrie_trieLookupPtr L 0 root addr' (by omega)
            (by simpa [Nat.mod_one] using hsub') haddr'
          rw [← hleaf_eq] at hsub'_end
          simp only [Subtrie, hne_leaf', ↓reduceIte] at hsub'_end
          have hf'_limbs := hsub'_end.2.2
          exact limbsAt_iff_pointwise.mpr ⟨hf'_limbs.lt_pow, fun m hm => by
            dsimp only; rw [hcp_vals m hm, hm1]; exact hf'_limbs.getElem hm⟩,
        fun q hq => by dsimp only; rw [hfr_cp q hq, hm1]⟩ ?_
      dsimp only [trieReadContract, mwCopyContract]
      wram_cost)
    (fun heq_leaf => by
      refine runs_seq_call_le hZero
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
        (by wram_words) ⟨dstPtr, L, rfl, hw1, hdst_w⟩ ?_
      rintro v mem' pos' ⟨dst', L', heq_z, rfl, hzero_list, hfr_z⟩
      simp only [List.cons.injEq, and_true] at heq_z
      rcases heq_z with ⟨rfl, rfl⟩
      refine runs_ret_le (by eval_expr) ⟨root, addrPtr, dstPtr, L, rfl, rfl,
        fun h' hp' f' addr' hsub' haddr' => by
          obtain ⟨hsub'_end, _⟩ := subtrie_trieLookupPtr L 0 root addr' (by omega)
            (by simpa [Nat.mod_one] using hsub') haddr'
          rw [heq_leaf] at hsub'_end
          simp only [Subtrie, ↓reduceIte] at hsub'_end
          simp only [Nat.mul_zero, Nat.add_zero] at hsub'_end
          rw [hsub'_end]
          exact limbsAt_zero_iff.mpr hzero_list,
        fun q hq => by dsimp only; rw [hfr_z q hq, hm1]⟩ ?_
      dsimp only [trieReadContract, mwZeroContract]
      wram_cost)

/-! ### Verification of `trieWrite` -/

theorem trieWrite_meetsContract {w : ℕ} {p : Program} {fProc arithBase : ℕ}
    (hCopy : MeetsContract w p (arithBase + idxCopy) (mwCopyContract w))
    (hProc : p.procs[fProc]? = some (trieWrite arithBase)) :
    MeetsContract w p fProc (trieWriteContract w) := by
  refine meetsContract_of_runs hProc ?_
  rintro args mem pos ω hwords ⟨rootPtr, hpPtr, addrPtr, valPtr, L, h, root, hp, f₀, addr, val,
    rfl, hL1, hh, hw2, hhp1, hmem_root, hmem_hp, hsub0, hz0, hbound, hroot_lt, hhp_lt, hrhp_ne,
    hroot_nin, hhp_nin, haddr_le, hval_le, haddr_nin, hval_nin, haddr, hval⟩
  have hB : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.one_le_pow h 2 (by norm_num)) hB
  have hL_w : L < 2 ^ w := by omega
  let ContInv (i : ℕ) (mem_i : ℕ → ℕ) (slotPtr hp_i : ℕ) : Prop :=
    ∀ (mem' : ℕ → ℕ) (hp' newChild : ℕ),
      hp_i ≤ hp' → ZeroFrom mem' hp' → mem' hpPtr = hp' →
      (∀ q, q ≠ slotPtr → q ≠ hpPtr →
        ¬ InTrie mem_i L h (L - i) (mem_i slotPtr) q → q < hp_i → mem' q = mem_i q) →
      mem' slotPtr = newChild →
      Subtrie mem' L h hp' (L - i) newChild
        (Function.update (fun q => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q))
          (addr / 2 ^ (i * h)) val) →
      (∀ q, InTrie mem' L h (L - i) newChild q →
        InTrie mem_i L h (L - i) (mem_i slotPtr) q ∨ (hp_i ≤ q ∧ q < hp')) →
      Subtrie mem' L h hp' L (mem' rootPtr) (Function.update f₀ addr val) ∧
      (∀ q, InTrie mem' L h L (mem' rootPtr) q →
        InTrie mem L h L root q ∨ (hp ≤ q ∧ q < hp')) ∧
      (∀ q, q ≠ rootPtr → q ≠ hpPtr → ¬ InTrie mem L h L root q → q < hp → mem' q = mem q)
  have hloop : Triple w p
      (fun st => st.mem = mem ∧ st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = addrPtr ∧
        st.regs 3 = valPtr ∧ st.regs 4 = L ∧ st.regs 5 = 2 ^ h ∧ st.regs 6 = rootPtr)
      (forRange 7 (.const 0) (.reg 4)
        (.assign 8 (.load (.reg 6)) ;;
         .cond (.reg 8) .nop
           (.assign 8 (.load (.reg 1)) ;;
            .store (.reg 1) (.bin .add (.reg 8) (.reg 5)) ;;
            .store (.reg 6) (.reg 8)) ;;
         .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
         .assign 6 (.bin .add (.reg 8) (.reg 9))))
      (normalPost fun st =>
        st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = addrPtr ∧ st.regs 3 = valPtr ∧
        st.regs 4 = L ∧ st.regs 5 = 2 ^ h ∧
        let slotPtr := st.regs 6
        let hp_L := st.mem hpPtr
        hp ≤ hp_L ∧ hp_L ≤ hp + L * 2 ^ h ∧ ZeroFrom st.mem hp_L ∧
        slotPtr < hp_L ∧ slotPtr ≠ hpPtr ∧
        (∀ m < L, addrPtr + m ≠ slotPtr ∧ valPtr + m ≠ slotPtr) ∧
        (∀ m < L, st.mem (addrPtr + m) = mem (addrPtr + m) ∧ st.mem (valPtr + m) = mem (valPtr + m)) ∧
        (∀ q, InTrie st.mem L h 0 (st.mem slotPtr) q → InTrie mem L h L root q ∨ (hp ≤ q ∧ q < hp_L)) ∧
        ¬ InTrie st.mem L h 0 (st.mem slotPtr) slotPtr ∧
        Subtrie st.mem L h hp_L 0 (st.mem slotPtr) (fun q => f₀ (addr + 2 ^ (L * h) * q)) ∧
        ContInv L st.mem slotPtr hp_L)
      (fun _ => (L - 0) * (32 + (Expr.reg 4).size + 8) + ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
    refine Triple.strengthen_post (Triple.forRange_const (w := w) (p := p) (r := 7)
      (P := fun st => st.mem = mem ∧ st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧
        st.regs 2 = addrPtr ∧ st.regs 3 = valPtr ∧ st.regs 4 = L ∧ st.regs 5 = 2 ^ h ∧ st.regs 6 = rootPtr)
      (lo := .const 0) (hi := .reg 4)
      (body :=
        .assign 8 (.load (.reg 6)) ;;
        .cond (.reg 8) .nop
          (.assign 8 (.load (.reg 1)) ;;
           .store (.reg 1) (.bin .add (.reg 8) (.reg 5)) ;;
           .store (.reg 6) (.reg 8)) ;;
        .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
        .assign 6 (.bin .add (.reg 8) (.reg 9)))
      (Inv := fun i st =>
        st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = addrPtr ∧ st.regs 3 = valPtr ∧
        st.regs 4 = L ∧ st.regs 5 = 2 ^ h ∧ st.regs 7 = i ∧
        let slotPtr := st.regs 6
        let hp_i := st.mem hpPtr
        hp ≤ hp_i ∧ hp_i ≤ hp + i * 2 ^ h ∧ ZeroFrom st.mem hp_i ∧
        slotPtr < hp_i ∧ slotPtr ≠ hpPtr ∧
        (∀ m < L, addrPtr + m ≠ slotPtr ∧ valPtr + m ≠ slotPtr) ∧
        (∀ m < L, st.mem (addrPtr + m) = mem (addrPtr + m) ∧ st.mem (valPtr + m) = mem (valPtr + m)) ∧
        (∀ q, InTrie st.mem L h (L - i) (st.mem slotPtr) q → InTrie mem L h L root q ∨ (hp ≤ q ∧ q < hp_i)) ∧
        ¬ InTrie st.mem L h (L - i) (st.mem slotPtr) slotPtr ∧
        Subtrie st.mem L h hp_i (L - i) (st.mem slotPtr) (fun q => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q)) ∧
        ContInv i st.mem slotPtr hp_i)
      32 0 L (Nat.zero_le L) hw1 (fun _ => hL_w)
      (fun st ⟨hm, r0, r1, r2, r3, r4, r5, r6⟩ => by
        refine ⟨by eval_expr, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
          by simp [r5], by simp, ?_⟩
        dsimp only
        have hst_slot : Function.update st.regs 7 0 6 = rootPtr := by simp [r6]
        rw [hm, hst_slot, hmem_hp, hmem_root, Nat.sub_zero]
        refine ⟨le_refl _, by omega, hz0, hroot_lt, hrhp_ne,
          fun m hmL => ⟨(haddr_nin m hmL).1, (hval_nin m hmL).1⟩,
          fun _ _ => ⟨rfl, rfl⟩,
          fun q hq => Or.inl hq,
          hroot_nin,
          by simpa [Nat.zero_mul, Nat.pow_zero, Nat.mod_one] using hsub0,
          fun mem' hp' newChild hhp_le hz' hhp' hfr' hslot' hsub' hfoot' => by
            simp only [Nat.sub_zero, Nat.zero_mul, Nat.pow_zero, Nat.mod_one, Nat.div_one,
              Nat.zero_add, Nat.one_mul] at hsub' hfoot'
            rw [← hslot'] at hsub' hfoot'
            refine ⟨hsub', fun q hq => by simpa [hmem_root] using hfoot' q hq,
              fun q hnr hnh hnin hq_hp => ?_⟩
            exact hfr' q hnr hnh (by simpa [hmem_root] using hnin) hq_hp⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h4 := hi.2.2.2.2.1; eval_expr)
      (fun i _ hiL => by
        intro st ω_it ⟨r0, r1, r2, r3, r4, r5, r7,
          hhp_ge, hhp_le, hz_i, hslot_lt, hslot_ne, hdisj_slot, hm_av,
          hin_sub, hslot_nin, hsub_i, hcont_i⟩
        set slotPtr := st.regs 6
        set hp_i := st.mem hpPtr
        set oldChild := st.mem slotPtr
        have hdepth : L - i = (L - (i + 1)) + 1 := by omega
        have hhp_i_w : hp_i < 2 ^ w := by
          have : i * 2 ^ h ≤ L * 2 ^ h := Nat.mul_le_mul_right _ (by omega)
          omega
        have hhp_next_w : hp_i + 2 ^ h < 2 ^ w := by
          have : (i + 1) * 2 ^ h ≤ L * 2 ^ h := Nat.mul_le_mul_right _ hiL
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        have hslot_w : slotPtr < 2 ^ w := lt_trans hslot_lt hhp_i_w
        have hold_w : oldChild < 2 ^ w := subtrie_root_lt hsub_i hhp_i_w hw1
        set dig := (addr / 2 ^ (i * h)) % 2 ^ h
        have hdig_lt : dig < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hdig_val : st.mem (addrPtr + i) = dig := by
          rw [(hm_av i hiL).1]; exact haddr.getElem hiL
        refine runs_start_le ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (by eval_expr) (rfl : st.mem slotPtr = oldChild)) ?_
        have hafter_alloc :
            ∀ (cur hp_n : ℕ) (mem_n : ℕ → ℕ) (st₁ : State),
              st₁.mem = mem_n →
              st₁.regs 0 = rootPtr → st₁.regs 1 = hpPtr → st₁.regs 2 = addrPtr →
              st₁.regs 3 = valPtr → st₁.regs 4 = L → st₁.regs 5 = 2 ^ h →
              st₁.regs 6 = slotPtr → st₁.regs 7 = i → st₁.regs 8 = cur →
              cur ≠ 0 → 1 ≤ cur → cur + 2 ^ h ≤ hp_n →
              hp_i ≤ hp_n → hp_n ≤ hp + (i + 1) * 2 ^ h →
              mem_n hpPtr = hp_n → mem_n slotPtr = cur → ZeroFrom mem_n hp_n →
              (∀ m < L, mem_n (addrPtr + m) = mem (addrPtr + m) ∧ mem_n (valPtr + m) = mem (valPtr + m)) →
              Subtrie mem_n L h hp_n (L - (i + 1)) (mem_n (cur + dig))
                (fun q => f₀ (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) →
              ¬ InTrie mem_n L h (L - (i + 1)) (mem_n (cur + dig)) (cur + dig) →
              (∀ q, InTrie mem_n L h (L - (i + 1)) (mem_n (cur + dig)) q →
                InTrie mem L h L root q ∨ (hp ≤ q ∧ q < hp_n)) →
              cur + dig < hp_n → cur + dig ≠ hpPtr →
              (∀ m < L, addrPtr + m ≠ cur + dig ∧ valPtr + m ≠ cur + dig) →
              ContInv (i + 1) mem_n (cur + dig) hp_n →
              ∀ ω', ∃ o st'' c, Runs w p ω'
                (.assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
                 .assign 6 (.bin .add (.reg 8) (.reg 9)))
                st₁ o st'' c ∧
                normalPost (fun st₂ =>
                  (st₂.regs 0 = rootPtr ∧ st₂.regs 1 = hpPtr ∧ st₂.regs 2 = addrPtr ∧
                    st₂.regs 3 = valPtr ∧ st₂.regs 4 = L ∧ st₂.regs 5 = 2 ^ h ∧
                    Function.update st₂.regs 7 (i + 1) 7 = i + 1 ∧
                    hp ≤ st₂.mem hpPtr ∧ st₂.mem hpPtr ≤ hp + (i + 1) * 2 ^ h ∧ ZeroFrom st₂.mem (st₂.mem hpPtr) ∧
                    st₂.regs 6 < st₂.mem hpPtr ∧ st₂.regs 6 ≠ hpPtr ∧
                    (∀ m < L, addrPtr + m ≠ st₂.regs 6 ∧ valPtr + m ≠ st₂.regs 6) ∧
                    (∀ m < L, st₂.mem (addrPtr + m) = mem (addrPtr + m) ∧ st₂.mem (valPtr + m) = mem (valPtr + m)) ∧
                    (∀ q, InTrie st₂.mem L h (L - (i + 1)) (st₂.mem (st₂.regs 6)) q →
                      InTrie mem L h L root q ∨ (hp ≤ q ∧ q < st₂.mem hpPtr)) ∧
                    ¬ InTrie st₂.mem L h (L - (i + 1)) (st₂.mem (st₂.regs 6)) (st₂.regs 6) ∧
                    Subtrie st₂.mem L h (st₂.mem hpPtr) (L - (i + 1)) (st₂.mem (st₂.regs 6))
                      (fun q => f₀ (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) ∧
                    ContInv (i + 1) st₂.mem (st₂.regs 6) (st₂.mem hpPtr)) ∧
                  st₂.regs 7 = i) o st'' ∧
                c ≤ 10 := by
          intro cur hp_n mem_n st₁ hm₁ rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 rr8
            hcur_ne hcur1 hcur_hp hhp_n_ge hhp_n_le hmem_nhp hmem_nslot hz_n hm_nav
            hsub_next hnin_next hfoot_next hcd_hp hcd_ne_hp hcd_av hcont_next ω'
          have hhp_n_w : hp_n < 2 ^ w := by
            have : (i + 1) * 2 ^ h ≤ L * 2 ^ h := Nat.mul_le_mul_right _ hiL
            omega
          have hcd_w : cur + dig < 2 ^ w := lt_trans hcd_hp hhp_n_w
          have hdig_val₁ : st₁.mem (addrPtr + i) = dig := by
            rw [hm₁, (hm_nav i hiL).1]; exact haddr.getElem hiL
          refine runs_start_le ?_
          refine runs_seq_assign_le
            (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) hdig_val₁) ?_
          refine runs_assign_le
            (Expr.eval_add (by eval_expr) (by eval_expr) hcd_w) ?_ (by wram_cost)
          refine ⟨⟨rr0, rr1, rr2, rr3, rr4, rr5, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rr7⟩
          · simp [hm₁, hmem_nhp]; exact le_trans hhp_ge hhp_n_ge
          · simp [hm₁, hmem_nhp]; exact hhp_n_le
          · simp [hm₁, hmem_nhp]; exact hz_n
          · simp [hm₁, hmem_nhp, hcd_hp]
          · simp [hcd_ne_hp]
          · simpa using hcd_av
          · simpa [hm₁] using hm_nav
          · simpa [hm₁, hmem_nhp] using hfoot_next
          · simpa [hm₁] using hnin_next
          · simpa [hm₁, hmem_nhp] using hsub_next
          · simpa [hm₁, hmem_nhp] using hcont_next
        refine runs_seq_cond_le (by eval_expr)
          (fun hne_old => by
            have hold_ne : oldChild ≠ 0 := hne_old
            have hsub_i' := hsub_i
            rw [hdepth] at hsub_i'
            simp only [Subtrie, hold_ne, ↓reduceIte] at hsub_i'
            rcases hsub_i' with ⟨hcur1, hcur_hp, hch, hdisj_pc, hsib⟩
            have hsub_next : Subtrie st.mem L h hp_i (L - (i + 1)) (st.mem (oldChild + dig))
                (fun q => f₀ (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
              have hc := hch dig hdig_lt
              simpa [dig, key_split_step] using hc
            have hcd_in : InTrie st.mem L h (L - i) oldChild (oldChild + dig) := by
              rw [hdepth]
              exact (inTrie_node_iff hold_ne).mpr (Or.inl ⟨by omega, Nat.add_lt_add_left hdig_lt _⟩)
            have hcd_foot : ∀ q, InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) q →
                InTrie mem L h L root q ∨ (hp ≤ q ∧ q < hp_i) := fun q hq => by
              apply hin_sub
              rw [hdepth]
              exact (inTrie_node_iff hold_ne).mpr (Or.inr ⟨dig, hdig_lt, hq⟩)
            have hcd_nin : ¬ InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) (oldChild + dig) :=
              fun hin => hdisj_pc dig hdig_lt (oldChild + dig) hin ⟨by omega, Nat.add_lt_add_left hdig_lt _⟩
            have hcd_ne_hp : oldChild + dig ≠ hpPtr := by
              intro heq
              rcases hin_sub hpPtr (by rw [← heq]; exact hcd_in) with hin_r | hhp_r
              · exact hhp_nin hin_r
              · omega
            have hcd_av : ∀ m < L, addrPtr + m ≠ oldChild + dig ∧ valPtr + m ≠ oldChild + dig := by
              intro m hmL
              constructor
              · intro heq
                rcases hin_sub (addrPtr + m) (by rw [heq]; exact hcd_in) with hin_r | hhp_r
                · exact (haddr_nin m hmL).2.2 hin_r
                · omega
              · intro heq
                rcases hin_sub (valPtr + m) (by rw [heq]; exact hcd_in) with hin_r | hhp_r
                · exact (hval_nin m hmL).2.2 hin_r
                · omega
            have hcont_next : ContInv (i + 1) st.mem (oldChild + dig) hp_i := by
              intro mem' hp' newChild hhp'_ge hz' hmem'_hp hfr' hmem'_slot hsub'_next hfoot'_next
              have hmem'_parent : mem' slotPtr = oldChild := by
                have hne_cd : slotPtr ≠ oldChild + dig := fun heq => by
                  rw [heq] at hslot_nin; exact hslot_nin hcd_in
                have hnin_ch : ¬ InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) slotPtr :=
                  fun hin => hslot_nin (by rw [hdepth]; exact (inTrie_node_iff hold_ne).mpr (Or.inr ⟨dig, hdig_lt, hin⟩))
                exact hfr' slotPtr hne_cd hslot_ne hnin_ch hslot_lt
              have hfr_parent : ∀ q, q ≠ slotPtr → q ≠ hpPtr → ¬ InTrie st.mem L h (L - i) oldChild q →
                  q < hp_i → mem' q = st.mem q := by
                intro q hnq hnh hnin hq_hp
                have hne_cd : q ≠ oldChild + dig := fun heq => by rw [heq] at hnin; exact hnin hcd_in
                have hnin_ch : ¬ InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) q :=
                  fun hin => hnin (by rw [hdepth]; exact (inTrie_node_iff hold_ne).mpr (Or.inr ⟨dig, hdig_lt, hin⟩))
                exact hfr' q hne_cd hnh hnin_ch hq_hp
              have hsib_eq : ∀ k < 2 ^ h, k ≠ dig → ∀ q,
                  InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + k)) q → mem' q = st.mem q := by
                intro k hk hne q hq
                have hq_bounds := inTrie_bounds (hch k hk) q hq
                have hq_ne_cd : q ≠ oldChild + dig := fun heq =>
                  hdisj_pc k hk q hq ⟨by omega, by omega⟩
                have hq_ne_hp : q ≠ hpPtr := fun heq => by
                  rcases hin_sub hpPtr (by
                    rw [← heq, hdepth]
                    exact (inTrie_node_iff hold_ne).mpr (Or.inr ⟨k, hk, hq⟩)) with hin_r | hhp_r
                  · exact hhp_nin hin_r
                  · omega
                have hq_nin_dig : ¬ InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) q :=
                  fun hin => hsib k dig hk hdig_lt hne q hq hin
                exact hfr' q hq_ne_cd hq_ne_hp hq_nin_dig hq_bounds.2
              have hmem'_sib : ∀ k < 2 ^ h, k ≠ dig → mem' (oldChild + k) = st.mem (oldChild + k) := by
                intro k hk hne
                have hne_cd : oldChild + k ≠ oldChild + dig := by omega
                have hne_hp : oldChild + k ≠ hpPtr := fun heq => by
                  rcases hin_sub hpPtr (by
                    rw [← heq, hdepth]
                    exact (inTrie_node_iff hold_ne).mpr (Or.inl ⟨by omega, Nat.add_lt_add_left hk _⟩)) with hin_r | hhp_r
                  · exact hhp_nin hin_r
                  · omega
                have hnin_dig : ¬ InTrie st.mem L h (L - (i + 1)) (st.mem (oldChild + dig)) (oldChild + k) :=
                  fun hin => hdisj_pc dig hdig_lt (oldChild + k) hin ⟨by omega, Nat.add_lt_add_left hk _⟩
                exact hfr' (oldChild + k) hne_cd hne_hp hnin_dig (by omega)
              have hsub'_cur : Subtrie mem' L h hp' (L - i) oldChild
                  (Function.update (fun q => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q))
                    (addr / 2 ^ (i * h)) val) := by
                rw [hdepth]
                simp only [Subtrie, hold_ne, ↓reduceIte]
                refine ⟨hcur1, le_trans hcur_hp hhp'_ge, ?_, ?_, ?_⟩
                · intro k hk
                  by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot]
                    refine subtrie_congr_func (fun q _ => ?_) hsub'_next
                    simp only [dig, Function.update_apply, key_decompose_iff hdig_lt, true_and,
                      div_mul_pow_step]
                    split_ifs with h1
                    · rfl
                    · simp [key_split_step]
                  · rw [hmem'_sib k hk hkd]
                    have hupd : ∀ q,
                        Function.update (fun q' => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q'))
                          (addr / 2 ^ (i * h)) val (k + 2 ^ h * q) =
                        f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * (k + 2 ^ h * q)) := by
                      intro q
                      have hne_rest : k + 2 ^ h * q ≠ addr / 2 ^ (i * h) := fun heq =>
                        hkd ((key_decompose_iff hk).mp heq).1
                      simp [Function.update_of_ne hne_rest]
                    refine subtrie_congr_func (fun q _ => (hupd q).symm) ?_
                    exact subtrie_mono_hp hhp'_ge (subtrie_congr_mem (hsib_eq k hk hkd) (hch k hk))
                · intro k hk p hp_in
                  by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot] at hp_in
                    rcases hfoot'_next p hp_in with hp_old | hp_new
                    · exact hdisj_pc dig hdig_lt p hp_old
                    · omega
                  · rw [hmem'_sib k hk hkd] at hp_in
                    rw [inTrie_congr_mem (L - (i + 1)) (st.mem (oldChild + k)) (hsib_eq k hk hkd) p] at hp_in
                    exact hdisj_pc k hk p hp_in
                · intro k₁ k₂ hk₁ hk₂ hne p hp1 hp2
                  by_cases hk1d : k₁ = dig
                  · subst hk1d
                    have hk2d : k₂ ≠ dig := hne.symm
                    rw [hmem'_slot] at hp1
                    rw [hmem'_sib k₂ hk₂ hk2d] at hp2
                    rw [inTrie_congr_mem (L - (i + 1)) (st.mem (oldChild + k₂)) (hsib_eq k₂ hk₂ hk2d) p] at hp2
                    rcases hfoot'_next p hp1 with hp1_old | hp1_new
                    · exact hsib dig k₂ hk₁ hk₂ hne p hp1_old hp2
                    · have hbd := inTrie_bounds (hch k₂ hk₂) p hp2; omega
                  · rw [hmem'_sib k₁ hk₁ hk1d] at hp1
                    rw [inTrie_congr_mem (L - (i + 1)) (st.mem (oldChild + k₁)) (hsib_eq k₁ hk₁ hk1d) p] at hp1
                    by_cases hk2d : k₂ = dig
                    · subst hk2d
                      rw [hmem'_slot] at hp2
                      rcases hfoot'_next p hp2 with hp2_old | hp2_new
                      · exact hsib k₁ dig hk₁ hk₂ hne p hp1 hp2_old
                      · have hbd := inTrie_bounds (hch k₁ hk₁) p hp1; omega
                    · rw [hmem'_sib k₂ hk₂ hk2d] at hp2
                      rw [inTrie_congr_mem (L - (i + 1)) (st.mem (oldChild + k₂)) (hsib_eq k₂ hk₂ hk2d) p] at hp2
                      exact hsib k₁ k₂ hk₁ hk₂ hne p hp1 hp2
              have hfoot'_cur : ∀ q, InTrie mem' L h (L - i) oldChild q →
                  InTrie st.mem L h (L - i) oldChild q ∨ (hp_i ≤ q ∧ q < hp') := by
                intro q hq
                rw [hdepth] at hq ⊢
                rw [inTrie_node_iff hold_ne] at hq
                rcases hq with hq_self | ⟨k, hk, hq_ch⟩
                · exact Or.inl ((inTrie_node_iff hold_ne).mpr (Or.inl hq_self))
                · by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot] at hq_ch
                    rcases hfoot'_next q hq_ch with hq_old | hq_new
                    · exact Or.inl ((inTrie_node_iff hold_ne).mpr (Or.inr ⟨dig, hdig_lt, hq_old⟩))
                    · exact Or.inr hq_new
                  · rw [hmem'_sib k hk hkd] at hq_ch
                    rw [inTrie_congr_mem (L - (i + 1)) (st.mem (oldChild + k)) (hsib_eq k hk hkd) q] at hq_ch
                    exact Or.inl ((inTrie_node_iff hold_ne).mpr (Or.inr ⟨k, hk, hq_ch⟩))
              exact hcont_i mem' hp' oldChild hhp'_ge hz' hmem'_hp hfr_parent hmem'_parent hsub'_cur hfoot'_cur
            refine runs_seq_nop_le ?_
            obtain ⟨o, st'', c, hr, hpost, hc⟩ := hafter_alloc oldChild hp_i st.mem
              ⟨st.mem, Function.update st.regs 8 oldChild, st.pos⟩ rfl (by simp [r0]) (by simp [r1])
              (by simp [r2]) (by simp [r3]) (by simp [r4]) (by simp [r5]) (by simp [slotPtr]) (by simp [r7])
              (by simp) hold_ne hcur1 hcur_hp (le_refl _)
              (by have : i * 2 ^ h ≤ (i + 1) * 2 ^ h := Nat.mul_le_mul_right _ (by omega); omega)
              rfl rfl hz_i hm_av hsub_next hcd_nin hcd_foot (by omega) hcd_ne_hp hcd_av hcont_next ω_it
            exact ⟨o, st'', c, hr, hpost, by wram_cost⟩)
          (fun heq_old => by
            have hold0 : oldChild = 0 := heq_old
            refine runs_seq_assoc_le ?_
            refine runs_seq_assign_le
              (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
            refine runs_seq_assoc_le ?_
            refine runs_seq_store_le (by eval_expr)
              (Expr.eval_add (by eval_expr) (by eval_expr) hhp_next_w) ?_
            refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
            set hp_n := hp_i + 2 ^ h
            set mem_n := Function.update (Function.update st.mem hpPtr hp_n) slotPtr hp_i
            have hhp_n_ge : hp_i ≤ hp_n := by omega
            have hhp_n_le : hp_n ≤ hp + (i + 1) * 2 ^ h := by
              have : (i + 1) * 2 ^ h = i * 2 ^ h + 2 ^ h := by ring
              omega
            have hmem_nhp : mem_n hpPtr = hp_n := by
              dsimp only [mem_n]; rw [Function.update_of_ne hslot_ne.symm, Function.update_self]
            have hmem_nslot : mem_n slotPtr = hp_i := by
              simp [mem_n]
            have hz_n : ZeroFrom mem_n hp_n :=
              ((hz_i.mono hhp_n_ge).update_lt (by omega)).update_lt (by omega)
            have hm_nav : ∀ m < L, mem_n (addrPtr + m) = mem (addrPtr + m) ∧
                mem_n (valPtr + m) = mem (valPtr + m) := by
              intro m hmL
              dsimp only [mem_n]
              have hav := hm_av m hmL
              have hdis := hdisj_slot m hmL
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne hdis.1, Function.update_of_ne (haddr_nin m hmL).2.1, hav.1]
              · rw [Function.update_of_ne hdis.2, Function.update_of_ne (hval_nin m hmL).2.1, hav.2]
            have hz_f0 : ∀ q < 2 ^ ((L - i) * h),
                f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q) = 0 := by
              have hsub_0 := hsub_i
              rw [hold0, hdepth] at hsub_0
              simp only [Subtrie, ↓reduceIte] at hsub_0
              simpa [hdepth] using hsub_0
            have hz_rem : ∀ q < 2 ^ ((L - (i + 1)) * h),
                f₀ (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q) = 0 := by
              intro q hq
              have hsum_lt : dig + 2 ^ h * q < 2 ^ ((L - i) * h) := by
                have hmul : 2 ^ ((L - i) * h) = 2 ^ h * 2 ^ ((L - (i + 1)) * h) := by
                  rw [hdepth, ← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
                rw [hmul]
                have hle1 : 2 ^ h * (q + 1) ≤ 2 ^ h * 2 ^ ((L - (i + 1)) * h) := Nat.mul_le_mul_left _ hq
                rw [Nat.mul_add, Nat.mul_one] at hle1
                omega
              simpa [dig, key_split_step] using hz_f0 (dig + 2 ^ h * q) hsum_lt
            have hmem_cd0 : mem_n (hp_i + dig) = 0 := by
              dsimp only [mem_n]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hz_i (hp_i + dig) (by omega)
            have hsub_next : Subtrie mem_n L h hp_n (L - (i + 1)) (mem_n (hp_i + dig))
                (fun q => f₀ (addr % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * q)) := by
              rw [hmem_cd0]
              by_cases hzero : L - (i + 1) = 0
              · rw [hzero]; simpa [Subtrie] using hz_rem 0 (by simp)
              · rcases Nat.exists_eq_succ_of_ne_zero hzero with ⟨d', hd'⟩
                have hz' := hz_rem
                rw [hd'] at hz' ⊢
                simpa [Subtrie] using hz'
            have hcont_next : ContInv (i + 1) mem_n (hp_i + dig) hp_n := by
              intro mem' hp' newChild hhp'_ge hz' hmem'_hp hfr' hmem'_slot hsub'_next hfoot'_next
              have hmem'_parent : mem' slotPtr = hp_i := by
                rw [hfr' slotPtr (by omega) hslot_ne
                  (by rw [hmem_cd0]; exact inTrie_zero_root _ _ _ _ _) (by omega)]
                exact hmem_nslot
              have hfr_parent : ∀ q, q ≠ slotPtr → q ≠ hpPtr →
                  ¬ InTrie st.mem L h (L - i) oldChild q → q < hp_i → mem' q = st.mem q := by
                intro q hnq hnh _ hq_hp
                have h1 := hfr' q (by omega) hnh
                  (by rw [hmem_cd0]; exact inTrie_zero_root _ _ _ _ _) (by omega)
                dsimp only [mem_n] at h1
                rwa [Function.update_of_ne hnq, Function.update_of_ne hnh] at h1
              have hmem'_sib : ∀ k < 2 ^ h, k ≠ dig → mem' (hp_i + k) = 0 := by
                intro k hk hkd
                have h1 := hfr' (hp_i + k) (by omega) (by omega)
                  (by rw [hmem_cd0]; exact inTrie_zero_root _ _ _ _ _) (by omega)
                dsimp only [mem_n] at h1
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at h1
                rw [h1]
                exact hz_i (hp_i + k) (by omega)
              have hsub'_cur : Subtrie mem' L h hp' (L - i) hp_i
                  (Function.update (fun q => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q))
                    (addr / 2 ^ (i * h)) val) := by
                rw [hdepth]
                simp only [Subtrie, show hp_i ≠ 0 by omega, ↓reduceIte]
                refine ⟨by omega, le_trans (by omega : hp_i + 2 ^ h ≤ hp_n) hhp'_ge, ?_, ?_, ?_⟩
                · intro k hk
                  by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot]
                    refine subtrie_congr_func (fun q _ => ?_) hsub'_next
                    simp only [dig, Function.update_apply, key_decompose_iff hdig_lt, true_and,
                      div_mul_pow_step]
                    split_ifs with h1
                    · rfl
                    · simp [key_split_step]
                  · rw [hmem'_sib k hk hkd]
                    have hz_sib : ∀ q < 2 ^ ((L - (i + 1)) * h),
                        Function.update (fun q' => f₀ (addr % 2 ^ (i * h) + 2 ^ (i * h) * q'))
                          (addr / 2 ^ (i * h)) val (k + 2 ^ h * q) = 0 := by
                      intro q hq
                      have hne_rest : k + 2 ^ h * q ≠ addr / 2 ^ (i * h) := fun heq =>
                        hkd ((key_decompose_iff hk).mp heq).1
                      rw [Function.update_of_ne hne_rest]
                      have hsum_lt : k + 2 ^ h * q < 2 ^ ((L - i) * h) := by
                        have hmul : 2 ^ ((L - i) * h) = 2 ^ h * 2 ^ ((L - (i + 1)) * h) := by
                          rw [hdepth, ← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
                        rw [hmul]
                        have hle1 : 2 ^ h * (q + 1) ≤ 2 ^ h * 2 ^ ((L - (i + 1)) * h) := Nat.mul_le_mul_left _ hq
                        rw [Nat.mul_add, Nat.mul_one] at hle1
                        omega
                      exact hz_f0 (k + 2 ^ h * q) hsum_lt
                    by_cases hzero : L - (i + 1) = 0
                    · rw [hzero]; simpa [Subtrie] using hz_sib 0 (by simp)
                    · rcases Nat.exists_eq_succ_of_ne_zero hzero with ⟨d', hd'⟩
                      have hz' := hz_sib
                      rw [hd'] at hz' ⊢
                      simpa [Subtrie] using hz'
                · intro k hk p hp_in
                  by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot] at hp_in
                    rcases hfoot'_next p hp_in with hp_old | hp_new
                    · rw [hmem_cd0] at hp_old; exact False.elim (inTrie_zero_root _ _ _ _ _ hp_old)
                    · omega
                  · rw [hmem'_sib k hk hkd] at hp_in
                    exact False.elim (inTrie_zero_root _ _ _ _ _ hp_in)
                · intro k₁ k₂ hk₁ hk₂ hne p hp1 hp2
                  by_cases hk1d : k₁ = dig
                  · subst hk1d
                    rw [hmem'_sib k₂ hk₂ hne.symm] at hp2
                    exact False.elim (inTrie_zero_root _ _ _ _ _ hp2)
                  · rw [hmem'_sib k₁ hk₁ hk1d] at hp1
                    exact False.elim (inTrie_zero_root _ _ _ _ _ hp1)
              have hfoot'_cur : ∀ q, InTrie mem' L h (L - i) hp_i q →
                  InTrie st.mem L h (L - i) oldChild q ∨ (hp_i ≤ q ∧ q < hp') := by
                intro q hq
                rw [hdepth] at hq
                rw [inTrie_node_iff (by omega)] at hq
                rcases hq with hq_self | ⟨k, hk, hq_ch⟩
                · exact Or.inr ⟨hq_self.1, lt_of_lt_of_le hq_self.2 (le_trans (le_refl hp_n) hhp'_ge)⟩
                · by_cases hkd : k = dig
                  · subst hkd
                    rw [hmem'_slot] at hq_ch
                    rcases hfoot'_next q hq_ch with hq_old | hq_new
                    · rw [hmem_cd0] at hq_old; exact False.elim (inTrie_zero_root _ _ _ _ _ hq_old)
                    · exact Or.inr ⟨le_trans (by omega : hp_i ≤ hp_n) hq_new.1, hq_new.2⟩
                  · rw [hmem'_sib k hk hkd] at hq_ch
                    exact False.elim (inTrie_zero_root _ _ _ _ _ hq_ch)
              exact hcont_i mem' hp' hp_i (le_trans hhp_n_ge hhp'_ge) hz' hmem'_hp
                hfr_parent hmem'_parent hsub'_cur hfoot'_cur
            obtain ⟨o, st'', c, hr, hpost, hc⟩ := hafter_alloc hp_i hp_n mem_n
              ⟨mem_n, Function.update (Function.update st.regs 8 (st.mem slotPtr)) 8 (st.mem hpPtr), st.pos⟩
              rfl (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4])
              (by simp [r5]) (by simp [slotPtr]) (by simp [r7]) (by simp [hp_i])
              (by omega) (by omega) (by omega) hhp_n_ge hhp_n_le hmem_nhp hmem_nslot hz_n
              hm_nav hsub_next (by rw [hmem_cd0]; exact inTrie_zero_root _ _ _ _ _)
              (fun q hq => by rw [hmem_cd0] at hq; exact False.elim (inTrie_zero_root _ _ _ _ _ hq))
              (by omega) (by omega) (fun m _ => ⟨by omega, by omega⟩) hcont_next ω_it
            exact ⟨o, st'', c, hr, hpost, by wram_cost⟩)))
      (fun o st hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨rr0, rr1, rr2, rr3, rr4, rr5, _,
            hhp1', hhp2', hz', hsl1, hsl2, hdis, hmav, hft, hni, hsu, hco⟩
          dsimp only at hhp1' hhp2' hz' hsl1 hsl2 hdis hmav hft hni hsu hco ⊢
          rw [Nat.sub_self] at hft hni hsu
          rw [Nat.mod_eq_of_lt haddr.lt_pow] at hsu
          exact ⟨rr0, rr1, rr2, rr3, rr4, rr5,
            hhp1', hhp2', hz', hsl1, hsl2, hdis, hmav, hft, hni, hsu, hco⟩)
  refine runs_start_le ?_
  dsimp only [trieWrite]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState]⟩ ?_
  rintro st_L ⟨r0, r1, r2, r3, r4, r5, hhp_L_ge, hhp_L_le, hz_L, hslot_L_lt, hslot_L_ne, hdisj_L, hm_av_L,
    hfoot_L, hnin_L, hsub_L, hcont_L⟩
  set slotPtr := st_L.regs 6
  set hp_L := st_L.mem hpPtr
  set oldLeaf := st_L.mem slotPtr
  have hhp_L_w : hp_L < 2 ^ w := by omega
  have hhp_end_w : hp_L + L < 2 ^ w := by omega
  have hslot_L_w : slotPtr < 2 ^ w := lt_trans hslot_L_lt hhp_L_w
  have holdLeaf_w : oldLeaf < 2 ^ w := subtrie_root_lt hsub_L hhp_L_w hw1
  have hafter_leaf :
      ∀ (leaf hp_e : ℕ) (mem_a : ℕ → ℕ) (st_a : State),
        st_a.mem = mem_a →
        st_a.regs 0 = rootPtr → st_a.regs 1 = hpPtr → st_a.regs 2 = addrPtr →
        st_a.regs 3 = valPtr → st_a.regs 4 = L → st_a.regs 5 = 2 ^ h →
        st_a.regs 9 = leaf →
        1 ≤ leaf → leaf + L ≤ hp_e → hp_L ≤ hp_e → hp_e ≤ hp + L * 2 ^ h + L →
        mem_a hpPtr = hp_e → mem_a slotPtr = leaf → ZeroFrom mem_a hp_e →
        LimbsAt mem_a valPtr L h val → LimbsAt mem_a addrPtr L h addr →
        (valPtr + L ≤ leaf ∨ leaf + L ≤ valPtr) →
        (∀ q, q ≠ slotPtr → q ≠ hpPtr → ¬ InTrie st_L.mem L h 0 oldLeaf q → q < hp_L →
          mem_a q = st_L.mem q) →
        (∀ q, leaf ≤ q → q < leaf + L → InTrie st_L.mem L h 0 oldLeaf q ∨ (hp_L ≤ q ∧ q < hp_e)) →
        ∃ o st' c, Runs w p ω
          (.call 8 (arithBase + idxCopy) [.reg 3, .reg 9, .reg 4] ;; .ret (.const 0))
          st_a o st' c ∧
          (trieWriteContract w).post [rootPtr, hpPtr, addrPtr, valPtr, L, 2 ^ h] mem o.value st'.mem ∧
          c ≤ 17 * L + 17 := by
    intro leaf hp_e mem_a st_a hm_a rr0 rr1 rr2 rr3 rr4 rr5 rr9
      hleaf1 hleaf_hp hhp_e_ge hhp_e_le hmem_ehp hmem_eslot hz_a hval_a haddr_a
      hdisj_vl hfr_a hleaf_foot
    have hhp_e_w : hp_e < 2 ^ w := by omega
    have hleaf_w : leaf + L < 2 ^ w := by omega
    refine runs_start_le ?_
    refine runs_seq_call_le hCopy
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
      (by wram_words) ⟨valPtr, leaf, L, rfl, hw1, by omega, hleaf_w,
        by rcases hdisj_vl with h | h; exact Or.inr (Or.inl h); exact Or.inl h⟩ ?_
    rintro v mem' pos' ⟨src_c, dst_c, L_c, heq_c, rfl, hcp_vals, hfr_cp⟩
    simp only [List.cons.injEq, and_true] at heq_c
    rcases heq_c with ⟨rfl, rfl, rfl⟩
    have hhp_notin_leaf : hpPtr < leaf ∨ leaf + L ≤ hpPtr := by
      by_contra hnot
      have h1 : leaf ≤ hpPtr := by omega
      have h2 : hpPtr < leaf + L := by omega
      rcases hleaf_foot hpPtr h1 h2 with h_in | h_new
      · rcases hfoot_L hpPtr h_in with h_root | h_hp
        · exact hhp_nin h_root
        · omega
      · omega
    have hhp_keep : mem' hpPtr = hp_e := by
      rw [hfr_cp hpPtr hhp_notin_leaf, hm_a, hmem_ehp]
    have hz_end : ZeroFrom mem' hp_e := by
      intro q hq
      rw [hfr_cp q (by omega), hm_a]
      exact hz_a q hq
    have hmem'_slot : mem' slotPtr = leaf := by
      have hne_vl : slotPtr < leaf ∨ leaf + L ≤ slotPtr := by
        by_contra hnot
        have hlt1 : leaf ≤ slotPtr := by omega
        have hlt2 : slotPtr < leaf + L := by omega
        rcases hleaf_foot slotPtr hlt1 hlt2 with h1 | h2
        · exact hnin_L h1
        · exact absurd h2.1 (Nat.not_le_of_gt hslot_L_lt)
      rw [hfr_cp slotPtr hne_vl, hm_a, hmem_eslot]
    have hfr_cont : ∀ q, q ≠ slotPtr → q ≠ hpPtr → ¬ InTrie st_L.mem L h 0 oldLeaf q → q < hp_L →
        mem' q = st_L.mem q := by
      intro q hnq hnh hnin hq_hp
      have hne_vl : q < leaf ∨ leaf + L ≤ q := by
        by_contra hnot
        have hlt1 : leaf ≤ q := by omega
        have hlt2 : q < leaf + L := by omega
        rcases hleaf_foot q hlt1 hlt2 with h1 | h2
        · exact hnin h1
        · exact absurd h2.1 (Nat.not_le_of_gt hq_hp)
      rw [hfr_cp q hne_vl, hm_a]
      exact hfr_a q hnq hnh hnin hq_hp
    have hval_limbs : LimbsAt mem' leaf L h val :=
      limbsAt_iff_pointwise.mpr ⟨hval.lt_pow, fun m hm => by
        rw [hcp_vals m hm, hm_a]; exact hval_a.getElem hm⟩
    have hsub'_leaf : Subtrie mem' L h hp_e (L - L) leaf
        (Function.update (fun q => f₀ (addr % 2 ^ (L * h) + 2 ^ (L * h) * q))
          (addr / 2 ^ (L * h)) val) := by
      have hdiv0 : addr / 2 ^ (L * h) = 0 := Nat.div_eq_of_lt haddr.lt_pow
      rw [Nat.sub_self, hdiv0]
      simp only [Subtrie, show leaf ≠ 0 by omega, ↓reduceIte, Function.update_self]
      exact ⟨hleaf1, hleaf_hp, hval_limbs⟩
    have hfoot'_leaf : ∀ q, InTrie mem' L h (L - L) leaf q →
        InTrie st_L.mem L h 0 oldLeaf q ∨ (hp_L ≤ q ∧ q < hp_e) := by
      intro q hq
      rw [Nat.sub_self, inTrie_leaf_iff (by omega)] at hq
      exact hleaf_foot q hq.1 hq.2
    obtain ⟨hsub_res, hfoot_res, hfr_res⟩ :=
      hcont_L mem' hp_e leaf hhp_e_ge hz_end hhp_keep
        (fun q hnq hnh hnin hq_hp =>
          hfr_cont q hnq hnh (by simpa [oldLeaf, Nat.sub_self] using hnin) hq_hp)
        hmem'_slot hsub'_leaf
        (fun q hq => by
          have hq' := hfoot'_leaf q (by simpa [oldLeaf, Nat.sub_self] using hq)
          simpa [oldLeaf, Nat.sub_self] using hq')
    refine runs_ret_le (by eval_expr)
      ⟨rootPtr, hpPtr, addrPtr, valPtr, L, 2 ^ h, rfl, rfl,
        by dsimp only; rw [hmem_hp, hhp_keep]; exact le_trans hhp_L_ge hhp_e_ge,
        by dsimp only; rw [hmem_hp, hhp_keep]; exact hhp_e_le,
        fun h' f' addr' val' hB_eq hsub' haddr' hval' => by
          have hh' : h = h' := Nat.pow_right_injective (by norm_num) hB_eq
          subst hh'
          rw [hmem_hp, hmem_root] at hsub'
          have ha_eq : addr' = addr := haddr'.ext haddr
          have hv_eq : val' = val := hval'.ext hval
          subst ha_eq; subst hv_eq
          have hsub_ext := subtrie_ext hsub' hsub0
          have hres' : Subtrie mem' L h (mem' hpPtr) L (mem' rootPtr) (Function.update f' addr' val') := by
            refine subtrie_congr_func (fun q hq => ?_) (by rwa [hhp_keep])
            by_cases hqa : q = addr'
            · subst hqa; simp
            · simp [Function.update_of_ne hqa, (hsub_ext q hq).symm]
          exact ⟨hres', by dsimp only; rw [hhp_keep, hmem_root, hmem_hp]; exact hfoot_res⟩,
        by dsimp only; rw [hhp_keep]; exact hz_end,
        fun h' p hB_eq hnp hnh hnin hp_lt => by
          have hh' : h = h' := Nat.pow_right_injective (by norm_num) hB_eq
          subst hh'
          rw [hmem_root] at hnin
          rw [hmem_hp] at hp_lt
          exact hfr_res p hnp hnh hnin hp_lt⟩ ?_
    dsimp only [mwCopyContract]
    wram_cost
  refine runs_seq_assign_le
    (Expr.eval_load_of_eq (by eval_expr) (rfl : st_L.mem slotPtr = oldLeaf)) ?_
  refine runs_seq_cond_le (by eval_expr)
    (fun hne_leaf => by
      have hold_ne : oldLeaf ≠ 0 := hne_leaf
      have hsub_L' := hsub_L
      simp only [Subtrie, hold_ne, ↓reduceIte] at hsub_L'
      rcases hsub_L' with ⟨hleaf1, hleaf_hp, _⟩
      have hdisj_vl : valPtr + L ≤ oldLeaf ∨ oldLeaf + L ≤ valPtr := by
        refine disjoint_range_of_inTrie (S := fun q => q < hp ∧ ¬ InTrie mem L h L root q)
          (fun m hm => ⟨by omega, (hval_nin m hm).2.2⟩) (fun m hm => ?_)
        have hin0 : InTrie st_L.mem L h 0 oldLeaf (oldLeaf + m) :=
          (inTrie_leaf_iff hold_ne).mpr ⟨by omega, by omega⟩
        intro ⟨hlt, hnin⟩
        rcases hfoot_L (oldLeaf + m) hin0 with h1 | h2
        · exact hnin h1
        · omega
      refine runs_seq_nop_le ?_
      have hhp_L_bound : hp_L ≤ hp + L * 2 ^ h + L := by omega
      obtain ⟨o, st', c, hr, hpost, hc⟩ := hafter_leaf oldLeaf hp_L st_L.mem
        ⟨st_L.mem, Function.update st_L.regs 9 oldLeaf, st_L.pos⟩ rfl
        (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4])
        (by simp [r5]) (by simp) hleaf1 hleaf_hp (le_refl _) hhp_L_bound rfl rfl hz_L
        (limbsAt_iff_pointwise.mpr ⟨hval.lt_pow, fun m hm => by
          rw [(hm_av_L m hm).2]; exact hval.getElem hm⟩)
        (limbsAt_iff_pointwise.mpr ⟨haddr.lt_pow, fun m hm => by
          rw [(hm_av_L m hm).1]; exact haddr.getElem hm⟩)
        hdisj_vl (fun q _ _ _ _ => rfl) (fun q hq1 hq2 => Or.inl ((inTrie_leaf_iff hold_ne).mpr ⟨hq1, hq2⟩))
      exact ⟨o, st', c, hr, hpost, by dsimp only [trieWriteContract]; wram_cost⟩)
    (fun heq_leaf => by
      have hold0 : oldLeaf = 0 := heq_leaf
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_store_le (by eval_expr)
        (Expr.eval_add (by eval_expr) (by eval_expr) hhp_end_w) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      set hp_e := hp_L + L
      set mem_a := Function.update (Function.update st_L.mem hpPtr hp_e) slotPtr hp_L
      have hmem_ehp : mem_a hpPtr = hp_e := by
        dsimp only [mem_a]; rw [Function.update_of_ne hslot_L_ne.symm, Function.update_self]
      have hmem_eslot : mem_a slotPtr = hp_L := by
        simp [mem_a]
      have hz_a : ZeroFrom mem_a hp_e :=
        ((hz_L.mono (by omega : hp_L ≤ hp_e)).update_lt (by omega)).update_lt (by omega)
      have hval_a : LimbsAt mem_a valPtr L h val :=
        limbsAt_iff_pointwise.mpr ⟨hval.lt_pow, fun m hm => by
          dsimp only [mem_a]
          rw [Function.update_of_ne (hdisj_L m hm).2, Function.update_of_ne (hval_nin m hm).2.1,
            (hm_av_L m hm).2]
          exact hval.getElem hm⟩
      have haddr_a : LimbsAt mem_a addrPtr L h addr :=
        limbsAt_iff_pointwise.mpr ⟨haddr.lt_pow, fun m hm => by
          dsimp only [mem_a]
          rw [Function.update_of_ne (hdisj_L m hm).1, Function.update_of_ne (haddr_nin m hm).2.1,
            (hm_av_L m hm).1]
          exact haddr.getElem hm⟩
      obtain ⟨o, st', c, hr, hpost, hc⟩ := hafter_leaf hp_L hp_e mem_a
        ⟨mem_a, Function.update (Function.update st_L.regs 9 (st_L.mem slotPtr)) 9 (st_L.mem hpPtr), st_L.pos⟩ rfl
        (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4])
        (by simp [r5]) (by simp [hp_L]) (by omega) (le_refl hp_e) (by omega) (by omega)
        hmem_ehp hmem_eslot hz_a hval_a haddr_a (Or.inl (by omega))
        (fun q hnq hnh _ _ => by
          dsimp only [mem_a]; rw [Function.update_of_ne hnq, Function.update_of_ne hnh])
        (fun q hq1 hq2 => Or.inr ⟨hq1, hq2⟩)
      exact ⟨o, st', c, hr, hpost, by dsimp only [trieWriteContract]; wram_cost⟩)

/-! ### Module wrappers -/

theorem trieModule_procs_at {p : Program} {b arithBase k : ℕ}
    (hp : p.HasAt b (trieModule arithBase)) (hk : k < (trieModule arithBase).length) :
    p.procs[b + k]? = some (trieModule arithBase)[k] :=
  hp k hk

theorem trieRead_of_trieModule {w : ℕ} {p : Program} {b arithBase : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt b (trieModule arithBase)) :
    MeetsContract w p (b + idxTrieRead) (trieReadContract w) := by
  refine trieRead_meetsContract (mwZero_of_arithModule hArith) (mwCopy_of_arithModule hArith) ?_
  have h := trieModule_procs_at hTrie (k := idxTrieRead) (by rw [trieModule_length]; decide)
  simpa [trieModule, idxTrieRead] using h

theorem trieWrite_of_trieModule {w : ℕ} {p : Program} {b arithBase : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt b (trieModule arithBase)) :
    MeetsContract w p (b + idxTrieWrite) (trieWriteContract w) := by
  refine trieWrite_meetsContract (mwCopy_of_arithModule hArith) ?_
  have h := trieModule_procs_at hTrie (k := idxTrieWrite) (by rw [trieModule_length]; decide)
  simpa [trieModule, idxTrieWrite] using h

end MinCostFlow.WideWord