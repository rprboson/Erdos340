import Mathlib

/-!
# Upper Bound Below 1/6 for Greedy Sidon and Mian–Chowla Sequences

This file formalizes a completely finitary, sorry-free proof that every greedy Sidon
sequence `a : ℕ → ℕ` generated from any finite initial Sidon set (and in particular
the explicitly constructed classical Mian–Chowla sequence `1, 2, 4, 8, 13, ...`)
satisfies:

  `∀ᶠ n in Filter.atTop, (a n : ℝ) / (n : ℝ) ^ 3 ≤ 1 / 6 - 1 / 12000000`

improving the classical cubic bound `a_n ≤ n^3 / 6 + O(n^2)`.

## Main Definitions and Theorems
* `IsCausallyCoveredFrom`: abstract causal coverage above a threshold `C`.
* `eventually_le_below_one_sixth`: finitary 4-bin proof for any causally covered sequence.
* `IsSidonSet` / `IsGreedySidonFrom`: standard definition of Sidon sets and greedy Sidon
  sequences from any finite initial prefix.
* `greedySidon_eventually_le_below_one_sixth`: quantitative bound `< 1/6` for every
  greedy Sidon sequence.
* `mianChowla` / `mianChowla_eventually_le_below_one_sixth`: explicit inductive construction
  of the Mian–Chowla sequence and its quantitative bound `< 1/6`.
-/

open Finset Filter

namespace MianChowla

/-- A strictly increasing sequence `a : ℕ → ℕ` is *causally covered above `C`* if every
integer `y` with `C < y < a n` outside `{a 0, ..., a (n-1)}` can be written as
`a i + a j = y + a k` for some `k < i ≤ j < n`. -/
structure IsCausallyCoveredFrom (a : ℕ → ℕ) (C : ℕ) : Prop where
  strictMono : StrictMono a
  covered : ∀ n y : ℕ, C < y → y < a n →
    (∃ i < n, a i = y) ∨ (∃ k i j, k < i ∧ i ≤ j ∧ j < n ∧ a i + a j = y + a k)

/-- The finite set of causal index triples `(k, i, j)` with `k < i ≤ j < r`. -/
def causalTriples (r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range r) ×ˢ ((range r) ×ˢ (range r))).filter (fun t => t.1 < t.2.1 ∧ t.2.1 ≤ t.2.2)

lemma mem_causalTriples {r k i j : ℕ} :
    (k, i, j) ∈ causalTriples r ↔ k < i ∧ i ≤ j ∧ j < r := by
  simp only [causalTriples, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨_, _, hj⟩, hki, hij⟩
    exact ⟨hki, hij, hj⟩
  · rintro ⟨hki, hij, hj⟩
    exact ⟨⟨by omega, by omega, hj⟩, hki, hij⟩

/-- Version-proof cardinality identity for `t \ s` when `s ⊆ t`. -/
lemma card_sdiff_add {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card + s.card = t.card := by
  have hdisj : Disjoint (t \ s) s := by
    rw [disjoint_left]
    intro x hx1 hx2
    exact (mem_sdiff.mp hx1).2 hx2
  have hunion : (t \ s) ∪ s = t := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx1 | hx2
      · exact (mem_sdiff.mp hx1).1
      · exact h hx2
    · intro hx
      rw [mem_union]
      by_cases hs : x ∈ s
      · right; exact hs
      · left; exact mem_sdiff.mpr ⟨hx, hs⟩
  rw [← card_union_of_disjoint hdisj, hunion]

/-- The number of pairs `(k, i)` with `k < i ≤ r` is `r * (r + 1) / 2`. -/
lemma card_pairs_lt_le (r : ℕ) :
    2 * (((range (r + 1)) ×ˢ (range (r + 1))).filter (fun p => p.1 < p.2)).card =
      r * (r + 1) := by
  induction r with
  | zero => decide
  | succ r ih =>
    have hsplit :
        (((range (r + 2)) ×ˢ (range (r + 2))).filter (fun p => p.1 < p.2)) =
        (((range (r + 1)) ×ˢ (range (r + 1))).filter (fun p => p.1 < p.2)) ∪
        ((range (r + 1)).image (fun k => (k, r + 1))) := by
      ext ⟨k, i⟩
      simp only [mem_filter, mem_product, mem_range, mem_union, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hk, hi⟩, hki⟩
        by_cases h : i = r + 1
        · right; exact ⟨k, by omega, rfl, h.symm⟩
        · left; exact ⟨⟨by omega, by omega⟩, hki⟩
      · rintro (⟨⟨hk, hi⟩, hki⟩ | ⟨k', hk', rfl, rfl⟩)
        · exact ⟨⟨by omega, by omega⟩, hki⟩
        · exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hdisj : Disjoint
        (((range (r + 1)) ×ˢ (range (r + 1))).filter (fun p => p.1 < p.2))
        ((range (r + 1)).image (fun k => (k, r + 1))) := by
      rw [disjoint_left]
      rintro ⟨k, i⟩ h1 h2
      simp only [mem_filter, mem_product, mem_range] at h1
      simp only [mem_image, mem_range, Prod.mk.injEq] at h2
      rcases h2 with ⟨_, _, _, rfl⟩
      omega
    have hinj : Function.Injective (fun k : ℕ => (k, r + 1)) :=
      fun _ _ h => by simpa using h
    rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injective _ hinj, card_range]
    linarith

/-- For any `s : Finset ℕ`, `2 * |{(i, j) ∈ s × s : i ≤ j}| = |s| * (|s| + 1)`. -/
lemma card_pairs_le_self (s : Finset ℕ) :
    2 * ((s ×ˢ s).filter (fun p => p.1 ≤ p.2)).card = s.card * (s.card + 1) := by
  let A := (s ×ˢ s).filter (fun p => p.1 ≤ p.2)
  let B := (s ×ˢ s).filter (fun p => p.2 ≤ p.1)
  have hAB : A ∪ B = s ×ˢ s := by
    ext ⟨x, y⟩
    simp only [A, B, mem_union, mem_filter, mem_product]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total x y with hxy | hyx
      · left; exact ⟨h, hxy⟩
      · right; exact ⟨h, hyx⟩
  have hInter : A ∩ B = s.image (fun x => (x, x)) := by
    ext ⟨x, y⟩
    simp only [A, B, mem_inter, mem_filter, mem_product, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, _⟩, h1⟩, ⟨_, h2⟩⟩
      exact ⟨x, hx, rfl, le_antisymm h1 h2⟩
    · rintro ⟨z, hz, rfl, rfl⟩
      exact ⟨⟨⟨hz, hz⟩, le_rfl⟩, ⟨⟨hz, hz⟩, le_rfl⟩⟩
  have hB : B = A.image (fun p => (p.2, p.1)) := by
    ext ⟨x, y⟩
    simp only [A, B, mem_filter, mem_product, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, hle⟩
      exact ⟨(y, x), ⟨⟨hy, hx⟩, hle⟩, rfl, rfl⟩
    · rintro ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, hle⟩, rfl, rfl⟩
      exact ⟨⟨hv, hu⟩, hle⟩
  have hswap_inj : Function.Injective (fun p : ℕ × ℕ => (p.2, p.1)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.2, h.1⟩
  have hcardB : B.card = A.card := by
    rw [hB]
    exact card_image_of_injective _ hswap_inj
  have hcardInter : (A ∩ B).card = s.card := by
    rw [hInter]
    exact card_image_of_injective _ (fun _ _ h => by simpa using h)
  have hsum := card_union_add_card_inter A B
  rw [hAB, hcardB, hcardInter, card_product] at hsum
  change 2 * A.card = s.card * (s.card + 1)
  nlinarith

/-- Exact algebraic identity: `6 * |T(r)| + r = r ^ 3` for all `r : ℕ`. -/
theorem card_causalTriples_exact (r : ℕ) :
    6 * (causalTriples r).card + r = r ^ 3 := by
  induction r with
  | zero => decide
  | succ r ih =>
    let pairs := ((range (r + 1)) ×ˢ (range (r + 1))).filter (fun p => p.1 < p.2)
    let top := pairs.image (fun p => (p.1, p.2, r))
    have hsplit : causalTriples (r + 1) = causalTriples r ∪ top := by
      ext ⟨k, i, j⟩
      simp only [mem_causalTriples, mem_union, top, pairs, mem_image, mem_filter,
        mem_product, mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨hki, hij, hj⟩
        by_cases h : j = r
        · right; exact ⟨(k, i), ⟨⟨by omega, by omega⟩, hki⟩, rfl, rfl, h.symm⟩
        · left; exact ⟨hki, hij, by omega⟩
      · rintro (⟨hki, hij, hj⟩ | ⟨⟨k', i'⟩, ⟨⟨_, hi'⟩, hki'⟩, rfl, rfl, rfl⟩)
        · exact ⟨hki, hij, by omega⟩
        · exact ⟨hki', by omega, by omega⟩
    have hdisj : Disjoint (causalTriples r) top := by
      rw [disjoint_left]
      rintro ⟨k, i, j⟩ h1 h2
      rw [mem_causalTriples] at h1
      simp only [top, mem_image, Prod.mk.injEq] at h2
      rcases h2 with ⟨_, _, _, _, rfl⟩
      omega
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1, p.2, r)) :=
      fun ⟨_, _⟩ ⟨_, _⟩ h => by simpa using h
    have htop : top.card = pairs.card := card_image_of_injective _ hinj
    have hpairs : 2 * pairs.card = r * (r + 1) := card_pairs_lt_le r
    rw [hsplit, card_union_of_disjoint hdisj, htop]
    nlinarith

/-- Number of elements of `a` with index `< n` that are `≤ B`. -/
def countLe (a : ℕ → ℕ) (n B : ℕ) : ℕ :=
  ((range n).filter (fun i => a i ≤ B)).card

lemma countLe_le_n (a : ℕ → ℕ) (n B : ℕ) : countLe a n B ≤ n := by
  simpa [countLe] using card_filter_le (range n) (fun i => a i ≤ B)

lemma countLe_mono (a : ℕ → ℕ) (n : ℕ) {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) :
    countLe a n B₁ ≤ countLe a n B₂ := by
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_range] at hi ⊢
  exact ⟨hi.1, le_trans hi.2 h⟩

/-- For a strictly increasing sequence, `a i ≤ B` iff `i < countLe a n B` (for `i < n`). -/
lemma lt_countLe_iff {a : ℕ → ℕ} (hmono : StrictMono a) {n B i : ℕ} (hi : i < n) :
    i < countLe a n B ↔ a i ≤ B := by
  have hset : (range n).filter (fun j => a j ≤ B) = range (countLe a n B) := by
    apply eq_of_subset_of_card_le
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      rw [mem_range]
      have hsub : range (j + 1) ⊆ (range n).filter (fun k => a k ≤ B) := by
        intro k hk
        rw [mem_range] at hk
        simp only [mem_filter, mem_range]
        exact ⟨by omega, le_trans (hmono.monotone (by omega)) hj.2⟩
      have hcard := card_le_card hsub
      rw [card_range] at hcard
      exact lt_of_lt_of_le (Nat.lt_succ_self j) hcard
    · simp [countLe]
  constructor
  · intro hlt
    have hmem : i ∈ (range n).filter (fun j => a j ≤ B) := by
      rw [hset, mem_range]; exact hlt
    exact (mem_filter.mp hmem).2
  · intro hle
    have hmem : i ∈ (range n).filter (fun j => a j ≤ B) :=
      mem_filter.mpr ⟨mem_range.mpr hi, hle⟩
    rw [hset, mem_range] at hmem
    exact hmem

/-- Finitary cubic lower bound: `6 * B ≤ r ^ 3 + 5 * r + 6 * C` for `B < a n`. -/
lemma lower_bound_count {a : ℕ → ℕ} {C : ℕ} (h : IsCausallyCoveredFrom a C)
    {n B : ℕ} (hB : B < a n) :
    6 * B ≤ (countLe a n B) ^ 3 + 5 * (countLe a n B) + 6 * C := by
  set r := countLe a n B
  let S := Ioc C B
  let A_img := (range r).image a
  let T_img := (causalTriples r).image (fun t => a t.2.1 + a t.2.2 - a t.1)
  have hsub : S ⊆ A_img ∪ T_img := by
    intro y hy
    simp only [S, mem_Ioc] at hy
    rw [mem_union]
    rcases h.covered n y hy.1 (lt_of_le_of_lt hy.2 hB) with
        ⟨i, hin, rfl⟩ | ⟨k, i, j, hki, hij, hjn, heq⟩
    · left
      rw [mem_image]
      exact ⟨i, mem_range.mpr ((lt_countLe_iff h.strictMono hin).mpr hy.2), rfl⟩
    · right
      have haj : a j < y := by
        have haki : a k < a i := h.strictMono hki
        omega
      have hjr : j < r := (lt_countLe_iff h.strictMono hjn).mpr (le_trans (le_of_lt haj) hy.2)
      rw [mem_image]
      refine ⟨(k, i, j), mem_causalTriples.mpr ⟨hki, hij, hjr⟩, ?_⟩
      dsimp only
      omega
  have hcard : B - C ≤ r + (causalTriples r).card := by
    calc B - C = S.card := by simp [S]
      _ ≤ (A_img ∪ T_img).card := card_le_card hsub
      _ ≤ A_img.card + T_img.card := card_union_le _ _
      _ ≤ r + (causalTriples r).card := by
        gcongr
        · exact le_trans card_image_le (by simp)
        · exact card_image_le
  have hex := card_causalTriples_exact r
  omega

/-- Elementary helper: `c > 0` and `c ^ 3 ≤ u ^ 3` imply `c ≤ u` on `ℝ`. -/
lemma cube_lb {u c : ℝ} (hc : 0 < c) (h : c ^ 3 ≤ u ^ 3) : c ≤ u := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < c ^ 2 + c * u + u ^ 2 := by nlinarith [sq_nonneg (u + c / 2)]
  have hmul : 0 < (c - u) * (c ^ 2 + c * u + u ^ 2) := mul_pos (by linarith) hpos
  nlinarith

/-- Pure polynomial contradiction on `ℝ` for the 4-bin parameters
(`ε = 1/1000`, `λ₀ = 1 - 1/2000000`, `h = 501/4000`, `t = 1503/2000`). -/
lemma four_bin_real_contradiction
    {lam u0 u2 u3 m err : ℝ}
    (hlam : 1 - (1 : ℝ) / 2000000 ≤ lam)
    (herr0 : 0 ≤ err)
    (herr : err ≤ 1 / 10000000)
    (hu0 : u0 ^ 3 ≥ 2 * (1 / 1000) * lam - err)
    (hu2 : u2 ^ 3 ≥ 2 * (501 / 4000) * lam - err)
    (hu3 : u3 ^ 3 ≥ 3 * (501 / 4000) * lam - err)
    (hu2_le : u2 ≤ u3)
    (hu3_le : u3 ≤ 1)
    (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1)
    (htail : 3 * u0 * m ^ 2 ≤ 1 - lam + err)
    (hcov : lam * (1 - 1503 / 2000) - err ≤
      3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) + (1 - (1 - m) ^ 3)) :
    False := by
  have hu0_lb : (12 : ℝ) / 100 ≤ u0 := cube_lb (by norm_num) (by linarith)
  have hu2_lb : (63 : ℝ) / 100 ≤ u2 := cube_lb (by norm_num) (by linarith)
  have hu3_lb : (721 : ℝ) / 1000 ≤ u3 := cube_lb (by norm_num) (by linarith)
  have hm_step : 3 * (12 / 100 : ℝ) * m ^ 2 ≤ 3 * u0 * m ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu0_lb) (sq_nonneg m)]
  have hm_sq : m ^ 2 ≤ ((13 : ℝ) / 10000) ^ 2 := by linarith
  have hm_ub : m ≤ (13 : ℝ) / 10000 := by nlinarith
  have hcore :
      3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) ≤
      3 * (63 / 100) * (1 - 721 / 1000) * (1 + 721 / 1000 - 2 * (63 / 100)) := by
    by_cases h2 : u2 ≤ 721 / 1000
    · have hdiff :
          3 * u2 * (1 - 721 / 1000) * (1 + 721 / 1000 - 2 * u2) -
          3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) =
          3 * u2 * ((u3 - 721 / 1000) * (u3 + 721 / 1000 - 2 * u2)) := by ring
      have hfac : 0 ≤ (u3 - 721 / 1000) * (u3 + 721 / 1000 - 2 * u2) :=
        mul_nonneg (by linarith) (by linarith)
      have hstep1 :
          3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) ≤
          3 * u2 * (1 - 721 / 1000) * (1 + 721 / 1000 - 2 * u2) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * u2) hfac]
      have hstep2 :
          3 * u2 * (1 - 721 / 1000) * (1 + 721 / 1000 - 2 * u2) ≤
          3 * (63 / 100) * (1 - 721 / 1000) * (1 + 721 / 1000 - 2 * (63 / 100)) := by
        nlinarith
      linarith
    · have hid :
          3 * u2 * (1 - u2) ^ 2 - 3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) =
          3 * u2 * (u3 - u2) ^ 2 := by ring
      have hstep1 : 3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) ≤ 3 * u2 * (1 - u2) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * u2) (sq_nonneg (u3 - u2))]
      have hsq : (1 - u2) ^ 2 ≤ (1 - 721 / 1000 : ℝ) ^ 2 := by nlinarith
      have hstep2 : 3 * u2 * (1 - u2) ^ 2 ≤ 3 * 1 * (1 - 721 / 1000 : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - u2) (sq_nonneg (1 - u2))]
      linarith
  have htail_cube : 1 - (1 - m) ^ 3 ≤ 3 * m := by
    have : 3 * m - (1 - (1 - m) ^ 3) = m ^ 2 * (3 - m) := by ring
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : (0 : ℝ) ≤ 3 - m)]
  nlinarith

/-- Main theorem (finitary form): for every sequence causally covered above `C`,
eventually `a n / n^3 ≤ 1/6 - 1/12000000`. -/
theorem eventually_le_below_one_sixth {a : ℕ → ℕ} {C : ℕ}
    (h : IsCausallyCoveredFrom a C) :
    ∀ᶠ n : ℕ in atTop, (a n : ℝ) / (n : ℝ) ^ 3 ≤ 1 / 6 - 1 / 12000000 := by
  rw [eventually_atTop]
  refine ⟨max 100000000 (C + 1), fun n hn => ?_⟩
  by_contra hgt
  push Not at hgt
  set M := a n
  have hn_big : 100000000 ≤ n := le_trans (le_max_left _ _) hn
  have hC_lt_n : C < n :=
    lt_of_lt_of_le (Nat.lt_succ_self C) (le_trans (le_max_right _ _) hn)
  have hn_r : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_big
  have hC_r : (C : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hC_lt_n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn2 : (100000000 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn3 : (100000000 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
  have hn3_pos : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos hn_pos 3
  have hn3_ne : (n : ℝ) ^ 3 ≠ 0 := ne_of_gt hn3_pos
  have hM_gt : (1 / 6 - 1 / 12000000 : ℝ) * (n : ℝ) ^ 3 < (M : ℝ) :=
    (lt_div_iff₀ hn3_pos).mp hgt
  have hM_ge_nr : (10000 : ℝ) * (n : ℝ) ≤ (M : ℝ) := by linarith
  have hM_ge_n : 10000 * n ≤ M := by exact_mod_cast hM_ge_nr
  have hM_ge : 10000 ≤ M := by omega
  have hC_lt_M : C < M := by omega
  -- Integer thresholds
  set B0 := M / 500
  set H := 501 * M / 4000 + 1
  set r0 := countLe a n B0
  set r2 := countLe a n (2 * H)
  set r3 := countLe a n (3 * H)
  set r4 := countLe a n (4 * H)
  have hB0_lt : B0 < M := by omega
  have h2H_lt : 2 * H < M := by omega
  have h3H_lt : 3 * H < M := by omega
  have h6H_lt : 6 * H + 1 < M := by omega
  have hC_lt_6H : C < 6 * H := by omega
  have hB0_le_4H : B0 ≤ 4 * H := by omega
  have hOver_ineq : M + B0 < 8 * H := by omega
  have hH_lb_nat : 501 * M < 4000 * H := by omega
  have hH_ub_nat : 4000 * H ≤ 501 * M + 4000 := by omega
  have hB0_lb_nat : M < 500 * (B0 + 1) := by omega
  have hr0_le_r4 : r0 ≤ r4 := countLe_mono a n hB0_le_4H
  have hr2_le_r3 : r2 ≤ r3 := countLe_mono a n (by omega)
  have hr3_le_r4 : r3 ≤ r4 := countLe_mono a n (by omega)
  have hr4_le_n : r4 ≤ n := countLe_le_n a n (4 * H)
  have hr0_le_n : r0 ≤ n := le_trans hr0_le_r4 hr4_le_n
  have hr3_le_n : r3 ≤ n := le_trans hr3_le_r4 hr4_le_n
  have hr2_le_n : r2 ≤ n := le_trans hr2_le_r3 hr3_le_n
  -- Normalized real variables
  let lam : ℝ := 6 * (M : ℝ) / (n : ℝ) ^ 3
  let err : ℝ := (1 : ℝ) / 10000000
  let u0 : ℝ := (r0 : ℝ) / (n : ℝ)
  let u2 : ℝ := (r2 : ℝ) / (n : ℝ)
  let u3 : ℝ := (r3 : ℝ) / (n : ℝ)
  let m : ℝ := ((n - r4 : ℕ) : ℝ) / (n : ℝ)
  have hlam_mul : lam * (n : ℝ) ^ 3 = 6 * (M : ℝ) := div_mul_cancel₀ _ hn3_ne
  have hlam : 1 - (1 : ℝ) / 2000000 ≤ lam := by
    have : lam = 6 * ((M : ℝ) / (n : ℝ) ^ 3) := by dsimp only [lam]; ring
    linarith
  have herr0 : 0 ≤ err := by norm_num [err]
  have herr : err ≤ 1 / 10000000 := by norm_num [err]
  have hu2_le : u2 ≤ u3 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hr2_le_r3) (le_of_lt hn_pos)
  have hu3_le : u3 ≤ 1 := (div_le_one hn_pos).mpr (by exact_mod_cast hr3_le_n)
  have hm0 : 0 ≤ m := div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)
  have hm1 : m ≤ 1 := (div_le_one hn_pos).mpr (by exact_mod_cast Nat.sub_le n r4)
  have hm_eq : m = ((n : ℝ) - (r4 : ℝ)) / (n : ℝ) := by
    dsimp only [m]; rw [Nat.cast_sub hr4_le_n]
  -- 1. Cubic lower bounds for u0, u2, u3
  have hu0 : u0 ^ 3 ≥ 2 * (1 / 1000) * lam - err := by
    have hlb := lower_bound_count h (n := n) (B := B0) hB0_lt
    have hlb_r : 6 * (B0 : ℝ) ≤ (r0 : ℝ) ^ 3 + 5 * (r0 : ℝ) + 6 * (C : ℝ) := by
      exact_mod_cast hlb
    have hB0_r : (M : ℝ) < 500 * ((B0 : ℝ) + 1) := by exact_mod_cast hB0_lb_nat
    have hr0_r : (r0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr0_le_n
    suffices hmul :
        (2 * (1 / 1000) * lam - err) * (n : ℝ) ^ 3 ≤ u0 ^ 3 * (n : ℝ) ^ 3 from
      le_of_mul_le_mul_right hmul hn3_pos
    have hL : (2 * (1 / 1000) * lam - err) * (n : ℝ) ^ 3 =
        6 * (M : ℝ) / 500 - err * (n : ℝ) ^ 3 := by
      calc (2 * (1 / 1000) * lam - err) * (n : ℝ) ^ 3
          = (1 / 500) * (lam * (n : ℝ) ^ 3) - err * (n : ℝ) ^ 3 := by ring
        _ = 6 * (M : ℝ) / 500 - err * (n : ℝ) ^ 3 := by rw [hlam_mul]; ring
    have hR : u0 ^ 3 * (n : ℝ) ^ 3 = (r0 : ℝ) ^ 3 := by
      dsimp only [u0]; rw [div_pow, div_mul_cancel₀ _ hn3_ne]
    rw [hL, hR]; dsimp only [err]; linarith
  have hu2 : u2 ^ 3 ≥ 2 * (501 / 4000) * lam - err := by
    have hlb := lower_bound_count h (n := n) (B := 2 * H) h2H_lt
    have hlb_r : 6 * (2 * (H : ℝ)) ≤ (r2 : ℝ) ^ 3 + 5 * (r2 : ℝ) + 6 * (C : ℝ) := by
      exact_mod_cast hlb
    have hH_r : 501 * (M : ℝ) < 4000 * (H : ℝ) := by exact_mod_cast hH_lb_nat
    have hr2_r : (r2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr2_le_n
    suffices hmul :
        (2 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3 ≤ u2 ^ 3 * (n : ℝ) ^ 3 from
      le_of_mul_le_mul_right hmul hn3_pos
    have hL : (2 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3 =
        12 * (501 / 4000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by
      calc (2 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3
          = 2 * (501 / 4000) * (lam * (n : ℝ) ^ 3) - err * (n : ℝ) ^ 3 := by ring
        _ = 12 * (501 / 4000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by rw [hlam_mul]; ring
    have hR : u2 ^ 3 * (n : ℝ) ^ 3 = (r2 : ℝ) ^ 3 := by
      dsimp only [u2]; rw [div_pow, div_mul_cancel₀ _ hn3_ne]
    rw [hL, hR]; dsimp only [err]; linarith
  have hu3 : u3 ^ 3 ≥ 3 * (501 / 4000) * lam - err := by
    have hlb := lower_bound_count h (n := n) (B := 3 * H) h3H_lt
    have hlb_r : 6 * (3 * (H : ℝ)) ≤ (r3 : ℝ) ^ 3 + 5 * (r3 : ℝ) + 6 * (C : ℝ) := by
      exact_mod_cast hlb
    have hH_r : 501 * (M : ℝ) < 4000 * (H : ℝ) := by exact_mod_cast hH_lb_nat
    have hr3_r : (r3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr3_le_n
    suffices hmul :
        (3 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3 ≤ u3 ^ 3 * (n : ℝ) ^ 3 from
      le_of_mul_le_mul_right hmul hn3_pos
    have hL : (3 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3 =
        18 * (501 / 4000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by
      calc (3 * (501 / 4000) * lam - err) * (n : ℝ) ^ 3
          = 3 * (501 / 4000) * (lam * (n : ℝ) ^ 3) - err * (n : ℝ) ^ 3 := by ring
        _ = 18 * (501 / 4000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by rw [hlam_mul]; ring
    have hR : u3 ^ 3 * (n : ℝ) ^ 3 = (r3 : ℝ) ^ 3 := by
      dsimp only [u3]; rw [div_pow, div_mul_cancel₀ _ hn3_ne]
    rw [hL, hR]; dsimp only [err]; linarith
  -- 2. Overflow tail bound: 3 * u0 * m^2 ≤ 1 - lam + err
  let f : ℕ × ℕ × ℕ → ℕ := fun t => a t.2.1 + a t.2.2 - a t.1
  let Over := (range r0) ×ˢ (((Ico r4 n) ×ˢ (Ico r4 n)).filter (fun p => p.1 ≤ p.2))
  have hOver_sub : Over ⊆ causalTriples n := by
    rintro ⟨k, i, j⟩ hmem
    simp only [Over, mem_product, mem_range, mem_filter, mem_Ico] at hmem
    rw [mem_causalTriples]
    omega
  have hOver_card : 6 * Over.card = 3 * r0 * (n - r4) * (n - r4 + 1) := by
    have h1 : Over.card =
        r0 * (((Ico r4 n) ×ˢ (Ico r4 n)).filter (fun p => p.1 ≤ p.2)).card := by
      simp [Over]
    have h2 : 2 * (((Ico r4 n) ×ˢ (Ico r4 n)).filter (fun p => p.1 ≤ p.2)).card =
        (n - r4) * (n - r4 + 1) := by
      simpa using card_pairs_le_self (Ico r4 n)
    calc 6 * Over.card
        = 3 * r0 * (2 * (((Ico r4 n) ×ˢ (Ico r4 n)).filter (fun p => p.1 ≤ p.2)).card) := by
          rw [h1]; ring
      _ = 3 * r0 * ((n - r4) * (n - r4 + 1)) := by rw [h2]
      _ = 3 * r0 * (n - r4) * (n - r4 + 1) := by ring
  have hOver_ge : 3 * r0 * (n - r4) ^ 2 ≤ 6 * Over.card := by
    rw [hOver_card]
    calc 3 * r0 * (n - r4) ^ 2
        = 3 * r0 * (n - r4) * (n - r4) := by ring
      _ ≤ 3 * r0 * (n - r4) * (n - r4 + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hcov_all :
      Ioc C (M - 1) ⊆ (range n).image a ∪ (causalTriples n \ Over).image f := by
    intro y hy
    simp only [mem_Ioc] at hy
    rw [mem_union]
    rcases h.covered n y hy.1 (by omega) with
        ⟨i, hin, rfl⟩ | ⟨k, i, j, hki, hij, hjn, heq⟩
    · left
      exact mem_image.mpr ⟨i, mem_range.mpr hin, rfl⟩
    · right
      refine mem_image.mpr ⟨(k, i, j),
        mem_sdiff.mpr ⟨mem_causalTriples.mpr ⟨hki, hij, hjn⟩, ?_⟩,
        by dsimp only [f]; omega⟩
      intro hmem
      simp only [Over, mem_product, mem_range, mem_filter, mem_Ico] at hmem
      have hak : a k ≤ B0 := (lt_countLe_iff h.strictMono (by omega)).mp hmem.1
      have hai : 4 * H < a i := by
        have hnot : ¬(i < r4) := by omega
        have hle := mt (lt_countLe_iff h.strictMono (by omega)).mpr hnot
        omega
      have haj : 4 * H < a j := by
        have hnot : ¬(j < r4) := by omega
        have hle := mt (lt_countLe_iff h.strictMono hjn).mpr hnot
        omega
      omega
  have htail_nat : 6 * M + 3 * r0 * (n - r4) ^ 2 ≤ n ^ 3 + 5 * n + 6 * C + 6 := by
    have hcard : M - 1 - C ≤ n + (causalTriples n \ Over).card := by
      calc M - 1 - C = (Ioc C (M - 1)).card := by simp
        _ ≤ ((range n).image a ∪ (causalTriples n \ Over).image f).card := card_le_card hcov_all
        _ ≤ ((range n).image a).card + ((causalTriples n \ Over).image f).card :=
          card_union_le _ _
        _ ≤ n + (causalTriples n \ Over).card := by
          gcongr
          · exact le_trans card_image_le (by simp)
          · exact card_image_le
    have hsdiff := card_sdiff_add hOver_sub
    have hex := card_causalTriples_exact n
    omega
  have htail : 3 * u0 * m ^ 2 ≤ 1 - lam + err := by
    have htail_r : 6 * (M : ℝ) + 3 * (r0 : ℝ) * ((n - r4 : ℕ) : ℝ) ^ 2 ≤
        (n : ℝ) ^ 3 + 5 * (n : ℝ) + 6 * (C : ℝ) + 6 := by exact_mod_cast htail_nat
    suffices hmul : (3 * u0 * m ^ 2) * (n : ℝ) ^ 3 ≤ (1 - lam + err) * (n : ℝ) ^ 3 from
      le_of_mul_le_mul_right hmul hn3_pos
    have hL : (3 * u0 * m ^ 2) * (n : ℝ) ^ 3 =
        3 * (r0 : ℝ) * ((n - r4 : ℕ) : ℝ) ^ 2 := by
      dsimp only [u0, m]; field_simp [hn_ne]
    have hR : (1 - lam + err) * (n : ℝ) ^ 3 =
        (n : ℝ) ^ 3 - 6 * (M : ℝ) + err * (n : ℝ) ^ 3 := by
      calc (1 - lam + err) * (n : ℝ) ^ 3
          = (n : ℝ) ^ 3 - lam * (n : ℝ) ^ 3 + err * (n : ℝ) ^ 3 := by ring
        _ = (n : ℝ) ^ 3 - 6 * (M : ℝ) + err * (n : ℝ) ^ 3 := by rw [hlam_mul]
    rw [hL, hR]; dsimp only [err]; linarith
  -- 3. Four-bin upper coverage bound on (6H, M - 1]
  let Core1 := (range r2) ×ˢ ((Ico r2 r3) ×ˢ (Ico r3 r4))
  let Core2 := (range r2) ×ˢ (((Ico r3 r4) ×ˢ (Ico r3 r4)).filter (fun p => p.1 ≤ p.2))
  let Tail := causalTriples n \ causalTriples r4
  have hTr4_sub : causalTriples r4 ⊆ causalTriples n := by
    rintro ⟨k, i, j⟩ hmem
    rw [mem_causalTriples] at hmem ⊢
    omega
  have hCore1_card : 6 * Core1.card ≤ 6 * r2 * (r3 - r2) * (n - r3) := by
    have h1 : Core1.card = r2 * ((r3 - r2) * (r4 - r3)) := by
      simp [Core1, card_product]
    have hle : r4 - r3 ≤ n - r3 := by omega
    have h2 : Core1.card ≤ r2 * ((r3 - r2) * (n - r3)) := by
      rw [h1]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
    calc 6 * Core1.card ≤ 6 * (r2 * ((r3 - r2) * (n - r3))) := Nat.mul_le_mul_left 6 h2
      _ = 6 * r2 * (r3 - r2) * (n - r3) := by ring
  have hCore2_card : 6 * Core2.card ≤ 3 * r2 * (n - r3) * (n - r3 + 1) := by
    have h1 : Core2.card =
        r2 * (((Ico r3 r4) ×ˢ (Ico r3 r4)).filter (fun p => p.1 ≤ p.2)).card := by
      simp [Core2]
    have h2 : 2 * (((Ico r3 r4) ×ˢ (Ico r3 r4)).filter (fun p => p.1 ≤ p.2)).card =
        (r4 - r3) * (r4 - r3 + 1) := by
      simpa using card_pairs_le_self (Ico r3 r4)
    have hle : r4 - r3 ≤ n - r3 := by omega
    have hmul1 : (r4 - r3) * (r4 - r3 + 1) ≤ (n - r3) * (n - r3 + 1) :=
      Nat.mul_le_mul hle (by omega)
    calc 6 * Core2.card
        = 3 * r2 * (2 * (((Ico r3 r4) ×ˢ (Ico r3 r4)).filter (fun p => p.1 ≤ p.2)).card) := by
          rw [h1]; ring
      _ = 3 * r2 * ((r4 - r3) * (r4 - r3 + 1)) := by rw [h2]
      _ ≤ 3 * r2 * ((n - r3) * (n - r3 + 1)) := Nat.mul_le_mul_left _ hmul1
      _ = 3 * r2 * (n - r3) * (n - r3 + 1) := by ring
  have hTail_card : 6 * Tail.card ≤ n ^ 3 - r4 ^ 3 := by
    have hsdiff : Tail.card + (causalTriples r4).card = (causalTriples n).card :=
      card_sdiff_add hTr4_sub
    have hexn := card_causalTriples_exact n
    have hexr := card_causalTriples_exact r4
    have hpow : r4 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hr4_le_n 3
    omega
  have hcov_hi :
      Ioc (6 * H) (M - 1) ⊆
      (((range n).image a ∪ Core1.image f) ∪ Core2.image f) ∪ Tail.image f := by
    intro y hy
    simp only [mem_Ioc] at hy
    rcases h.covered n y (by omega) (by omega) with
        ⟨i, hin, rfl⟩ | ⟨k, i, j, hki, hij, hjn, heq⟩
    · simp only [mem_union]
      left; left; left
      exact mem_image.mpr ⟨i, mem_range.mpr hin, rfl⟩
    · by_cases hj4 : r4 ≤ j
      · simp only [mem_union]
        right
        refine mem_image.mpr ⟨(k, i, j),
          mem_sdiff.mpr ⟨mem_causalTriples.mpr ⟨hki, hij, hjn⟩, ?_⟩,
          by dsimp only [f]; omega⟩
        rw [mem_causalTriples]
        omega
      · push Not at hj4
        have haj4 : a j ≤ 4 * H := (lt_countLe_iff h.strictMono hjn).mp hj4
        have hai4 : a i ≤ 4 * H := le_trans (h.strictMono.monotone hij) haj4
        have hi_ge_r2 : r2 ≤ i := by
          by_contra hlt
          push Not at hlt
          have hai2 : a i ≤ 2 * H := (lt_countLe_iff h.strictMono (by omega)).mp hlt
          omega
        have hj_ge_r3 : r3 ≤ j := by
          by_contra hlt
          push Not at hlt
          have haj3 : a j ≤ 3 * H := (lt_countLe_iff h.strictMono hjn).mp hlt
          have hai3 : a i ≤ 3 * H := le_trans (h.strictMono.monotone hij) haj3
          omega
        have hk_lt_r2 : k < r2 := by
          by_contra hge
          push Not at hge
          have hak2 : 2 * H < a k := by
            have hnot : ¬(k < r2) := by omega
            have hle := mt (lt_countLe_iff h.strictMono (by omega)).mpr hnot
            omega
          omega
        by_cases hi3 : i < r3
        · simp only [mem_union]
          left; left; right
          refine mem_image.mpr ⟨(k, i, j), ?_, by dsimp only [f]; omega⟩
          simp only [Core1, mem_product, mem_range, mem_Ico]
          exact ⟨hk_lt_r2, ⟨hi_ge_r2, hi3⟩, ⟨hj_ge_r3, hj4⟩⟩
        · simp only [mem_union]
          left; right
          refine mem_image.mpr ⟨(k, i, j), ?_, by dsimp only [f]; omega⟩
          simp only [Core2, mem_product, mem_range, mem_filter, mem_Ico]
          exact ⟨hk_lt_r2, ⟨⟨by omega, by omega⟩, ⟨hj_ge_r3, hj4⟩⟩, hij⟩
  have hcov_nat :
      6 * (M - 1 - 6 * H) ≤
      6 * n + 6 * r2 * (r3 - r2) * (n - r3) +
      3 * r2 * (n - r3) * (n - r3 + 1) + (n ^ 3 - r4 ^ 3) := by
    have hcard : M - 1 - 6 * H ≤ n + Core1.card + Core2.card + Tail.card := by
      have h0 : (Ioc (6 * H) (M - 1)).card = M - 1 - 6 * H := by simp
      have h1 := card_le_card hcov_hi
      have h2 := card_union_le (((range n).image a ∪ Core1.image f) ∪ Core2.image f) (Tail.image f)
      have h3 := card_union_le ((range n).image a ∪ Core1.image f) (Core2.image f)
      have h4 := card_union_le ((range n).image a) (Core1.image f)
      have hcA : ((range n).image a).card ≤ n := le_trans card_image_le (by simp)
      have hc1 : (Core1.image f).card ≤ Core1.card := card_image_le
      have hc2 : (Core2.image f).card ≤ Core2.card := card_image_le
      have hcT : (Tail.image f).card ≤ Tail.card := card_image_le
      omega
    omega
  have hcov :
      lam * (1 - 1503 / 2000) - err ≤
      3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) + (1 - (1 - m) ^ 3) := by
    have hcov_r :
        6 * ((M - 1 - 6 * H : ℕ) : ℝ) ≤
        6 * (n : ℝ) +
        6 * (r2 : ℝ) * ((r3 - r2 : ℕ) : ℝ) * ((n - r3 : ℕ) : ℝ) +
        3 * (r2 : ℝ) * ((n - r3 : ℕ) : ℝ) * (((n - r3 : ℕ) : ℝ) + 1) +
        ((n ^ 3 - r4 ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcov_nat
    rw [Nat.cast_sub (by omega : 6 * H ≤ M - 1), Nat.cast_sub (by omega : 1 ≤ M),
      Nat.cast_sub hr2_le_r3, Nat.cast_sub hr3_le_n,
      Nat.cast_sub (Nat.pow_le_pow_left hr4_le_n 3)] at hcov_r
    push_cast at hcov_r
    have hH_ub_r : 4000 * (H : ℝ) ≤ 501 * (M : ℝ) + 4000 := by exact_mod_cast hH_ub_nat
    have hr2_r : (r2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr2_le_n
    have hr3_r : (r3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr3_le_n
    have hcross : 3 * (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) ≤ 3 * (n : ℝ) ^ 2 := by
      have h1 : (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) ≤ (n : ℝ) * (n : ℝ) :=
        mul_le_mul hr2_r (by linarith [Nat.cast_nonneg (α := ℝ) r3])
          (by linarith) (le_of_lt hn_pos)
      rw [← sq] at h1
      linarith
    suffices hmul :
        (lam * (1 - 1503 / 2000) - err) * (n : ℝ) ^ 3 ≤
        (3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) + (1 - (1 - m) ^ 3)) * (n : ℝ) ^ 3 from
      le_of_mul_le_mul_right hmul hn3_pos
    have hL : (lam * (1 - 1503 / 2000) - err) * (n : ℝ) ^ 3 =
        6 * (1 - 1503 / 2000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by
      calc (lam * (1 - 1503 / 2000) - err) * (n : ℝ) ^ 3
          = (1 - 1503 / 2000) * (lam * (n : ℝ) ^ 3) - err * (n : ℝ) ^ 3 := by ring
        _ = 6 * (1 - 1503 / 2000) * (M : ℝ) - err * (n : ℝ) ^ 3 := by rw [hlam_mul]; ring
    have hR : (3 * u2 * (1 - u3) * (1 + u3 - 2 * u2) + (1 - (1 - m) ^ 3)) * (n : ℝ) ^ 3 =
        3 * (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) * ((n : ℝ) + (r3 : ℝ) - 2 * (r2 : ℝ)) +
        ((n : ℝ) ^ 3 - (r4 : ℝ) ^ 3) := by
      rw [hm_eq]; dsimp only [u2, u3]; field_simp [hn_ne]; ring
    rw [hL, hR]; dsimp only [err]
    have hpoly :
        6 * (r2 : ℝ) * ((r3 : ℝ) - (r2 : ℝ)) * ((n : ℝ) - (r3 : ℝ)) +
        3 * (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) * ((n : ℝ) - (r3 : ℝ) + 1) =
        3 * (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) * ((n : ℝ) + (r3 : ℝ) - 2 * (r2 : ℝ)) +
        3 * (r2 : ℝ) * ((n : ℝ) - (r3 : ℝ)) := by ring
    linarith
  exact four_bin_real_contradiction hlam herr0 herr hu0 hu2 hu3 hu2_le hu3_le hm0 hm1 htail hcov

/-! ## Bridge: Greedy Sidon Sequences and Explicit Mian–Chowla Construction -/

/-- A set `S : Set ℕ` is a Sidon set (`B₂`-set) if all unordered pairwise sums
`x + y` (`x ≤ y`) with `x, y ∈ S` are distinct. -/
def IsSidonSet (S : Set ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S,
    x ≤ y → z ≤ w → x + y = z + w → x = z ∧ y = w

lemma not_isSidonSet_imp {S : Set ℕ} (h : ¬ IsSidonSet S) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ z ∈ S, ∃ w ∈ S,
      u ≤ v ∧ z ≤ w ∧ u + v = z + w ∧ ¬ (u = z ∧ v = w) := by
  by_contra hno
  apply h
  intro u hu v hv z hz w hw huv hzw heq
  by_contra hne
  exact hno ⟨u, hu, v, hv, z, hz, w, hw, huv, hzw, heq, hne⟩

/-- Adding an element strictly larger than `2 * M` preserves the Sidon property
of any Sidon set bounded above by `M`. -/
lemma isSidonSet_insert_of_gt_two_mul {S : Set ℕ} {M x : ℕ}
    (hS : IsSidonSet S) (hM : ∀ s ∈ S, s ≤ M) (hx : 2 * M < x) :
    IsSidonSet (insert x S) := by
  intro u hu v hv z hz w hw huv hzw heq
  have hlt : ∀ s ∈ S, 2 * s < x := fun s hs => by have := hM s hs; omega
  have hle : ∀ t ∈ insert x S, t ≤ x := by
    intro t ht
    rcases Set.mem_insert_iff.mp ht with htx | htS
    · omega
    · have := hlt t htS; omega
  rcases Set.mem_insert_iff.mp hv with hvx | hvS
  · rcases Set.mem_insert_iff.mp hu with hux | _
    · have hzle := hle z hz
      have hwle := hle w hw
      omega
    · rcases Set.mem_insert_iff.mp hw with hwx | hwS
      · omega
      · have := hlt w hwS
        omega
  · have huS : u ∈ S := by
      rcases Set.mem_insert_iff.mp hu with hux | huS
      · have := hlt v hvS; omega
      · exact huS
    have hwS : w ∈ S := by
      rcases Set.mem_insert_iff.mp hw with hwx | hwS
      · have := hlt v hvS; omega
      · exact hwS
    have hzS : z ∈ S := by
      rcases Set.mem_insert_iff.mp hz with hzx | hzS
      · have := hlt w hwS; omega
      · exact hzS
    exact hS u huS v hvS z hzS w hwS huv hzw heq

/-- Helper: if `u + y = z + w` with `u, z, w ∈ {a 0, ..., a m}` and `a m < y`,
then `y` is represented by a causal triple `a i + a j = y + a k` with `k < i ≤ j ≤ m`. -/
lemma exists_causal_of_sum_eq {a : ℕ → ℕ} (hmono : StrictMono a) {m y u z w : ℕ}
    (hy : a m < y) (hzw : z ≤ w) (heq : u + y = z + w)
    (hu : u ∈ (range (m + 1)).image a)
    (hz : z ∈ (range (m + 1)).image a)
    (hw : w ∈ (range (m + 1)).image a) :
    ∃ k i j, k < i ∧ i ≤ j ∧ j ≤ m ∧ a i + a j = y + a k := by
  rcases mem_image.mp hu with ⟨k, hk, rfl⟩
  rcases mem_image.mp hz with ⟨i, hi, rfl⟩
  rcases mem_image.mp hw with ⟨j, hj, rfl⟩
  rw [mem_range] at hk hi hj
  have haj_lt : a j < y := lt_of_le_of_lt (hmono.monotone (by omega)) hy
  have hij : i ≤ j := by
    by_contra hlt
    push Not at hlt
    have := hmono hlt
    omega
  have hki : k < i := by
    by_contra hle
    push Not at hle
    have := hmono.monotone hle
    omega
  exact ⟨k, i, j, hki, hij, by omega, by omega⟩

/-- If `{a 0, ..., a m}` is Sidon and inserting `y > a m` breaks the Sidon property,
then `y` is blocked by a causal triple `a i + a j = y + a k` with `k < i ≤ j ≤ m`. -/
lemma not_isSidon_insert_gt_imp_causal {a : ℕ → ℕ} (hmono : StrictMono a) {m y : ℕ}
    (hy : a m < y)
    (hSidon : IsSidonSet (((range (m + 1)).image a : Finset ℕ) : Set ℕ))
    (hnot : ¬ IsSidonSet (insert y (((range (m + 1)).image a : Finset ℕ) : Set ℕ))) :
    ∃ k i j, k < i ∧ i ≤ j ∧ j ≤ m ∧ a i + a j = y + a k := by
  let S : Finset ℕ := (range (m + 1)).image a
  have hS_lt : ∀ t ∈ (S : Set ℕ), t < y := by
    intro t ht
    rcases mem_image.mp (Finset.mem_coe.mp ht) with ⟨idx, hidx, rfl⟩
    rw [mem_range] at hidx
    exact lt_of_le_of_lt (hmono.monotone (by omega)) hy
  change ¬ IsSidonSet (insert y (S : Set ℕ)) at hnot
  rcases not_isSidonSet_imp hnot with ⟨u, hu, v, hv, z, hz, w, hw, huv, hzw, heq, hne⟩
  rcases Set.mem_insert_iff.mp hv with rfl | hvS
  · rcases Set.mem_insert_iff.mp hw with rfl | hwS
    · exfalso; apply hne; omega
    · have hzS : z ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hz with rfl | hzS
        · have := hS_lt w hwS; omega
        · exact hzS
      have huS : u ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hu with rfl | huS
        · have := hS_lt w hwS; omega
        · exact huS
      exact exists_causal_of_sum_eq hmono hy hzw heq
        (Finset.mem_coe.mp huS) (Finset.mem_coe.mp hzS) (Finset.mem_coe.mp hwS)
  · rcases Set.mem_insert_iff.mp hw with rfl | hwS
    · have huS : u ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hu with rfl | huS
        · have := hS_lt v hvS; omega
        · exact huS
      have hzS : z ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hz with rfl | hzS
        · have := hS_lt v hvS; omega
        · exact hzS
      exact exists_causal_of_sum_eq hmono hy huv heq.symm
        (Finset.mem_coe.mp hzS) (Finset.mem_coe.mp huS) (Finset.mem_coe.mp hvS)
    · have huS : u ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hu with rfl | huS
        · have := hS_lt v hvS; omega
        · exact huS
      have hzS : z ∈ (S : Set ℕ) := by
        rcases Set.mem_insert_iff.mp hz with rfl | hzS
        · have := hS_lt w hwS; omega
        · exact hzS
      exact absurd (hSidon u huS v hvS z hzS w hwS huv hzw heq) hne

/-- A strictly increasing sequence `a : ℕ → ℕ` is a *greedy Sidon sequence from index `n₀`*
if every prefix `{a 0, ..., a m}` (`m ≥ n₀`) is a Sidon set and every integer strictly
between `a m` and `a (m + 1)` breaks the Sidon property. -/
structure IsGreedySidonFrom (a : ℕ → ℕ) (n₀ : ℕ) : Prop where
  strictMono : StrictMono a
  prefix_sidon : ∀ m, n₀ ≤ m → IsSidonSet (((range (m + 1)).image a : Finset ℕ) : Set ℕ)
  greedy_min : ∀ m y, n₀ ≤ m → a m < y → y < a (m + 1) →
    ¬ IsSidonSet (insert y (((range (m + 1)).image a : Finset ℕ) : Set ℕ))

/-- Every greedy Sidon sequence from index `n₀` is causally covered above `a n₀`. -/
theorem IsGreedySidonFrom.isCausallyCoveredFrom {a : ℕ → ℕ} {n₀ : ℕ}
    (hg : IsGreedySidonFrom a n₀) : IsCausallyCoveredFrom a (a n₀) where
  strictMono := hg.strictMono
  covered := by
    intro n y hy_gt hy_lt
    have hn₀_lt_n : n₀ < n := by
      by_contra hle
      push Not at hle
      have : a n ≤ a n₀ := hg.strictMono.monotone hle
      omega
    set r := countLe a n y
    have hr_gt : n₀ < r := (lt_countLe_iff hg.strictMono hn₀_lt_n).mpr (le_of_lt hy_gt)
    have hr_le : r ≤ n := countLe_le_n a n y
    set m := r - 1
    have hm_ge : n₀ ≤ m := by omega
    have hm_lt_n : m < n := by omega
    have ham_le : a m ≤ y := (lt_countLe_iff hg.strictMono hm_lt_n).mp (by omega)
    by_cases heq : a m = y
    · left; exact ⟨m, hm_lt_n, heq⟩
    · right
      have ham_lt : a m < y := lt_of_le_of_ne ham_le heq
      have hy_lt_succ : y < a (m + 1) := by
        by_cases hrn : r = n
        · have : m + 1 = n := by omega
          rw [this]; exact hy_lt
        · have hr_lt_n : r < n := by omega
          have hnot : ¬ (a r ≤ y) :=
            mt (lt_countLe_iff hg.strictMono hr_lt_n).mpr (lt_irrefl r)
          have : m + 1 = r := by omega
          rw [this]; omega
      rcases not_isSidon_insert_gt_imp_causal hg.strictMono ham_lt
          (hg.prefix_sidon m hm_ge) (hg.greedy_min m y hm_ge ham_lt hy_lt_succ) with
          ⟨k, i, j, hki, hij, hjm, hsum⟩
      exact ⟨k, i, j, hki, hij, by omega, hsum⟩

/-- Quantitative theorem for all greedy Sidon sequences starting from any finite initial
Sidon set: eventually `a n / n^3 ≤ 1/6 - 1/12000000`. -/
theorem greedySidon_eventually_le_below_one_sixth {a : ℕ → ℕ} {n₀ : ℕ}
    (hg : IsGreedySidonFrom a n₀) :
    ∀ᶠ n : ℕ in atTop, (a n : ℝ) / (n : ℝ) ^ 3 ≤ 1 / 6 - 1 / 12000000 :=
  eventually_le_below_one_sixth hg.isCausallyCoveredFrom

/-! ### Explicit Construction of the Classical Mian–Chowla Sequence -/

private structure SidonState where
  last : ℕ
  elems : Finset ℕ
  sidon : IsSidonSet (elems : Set ℕ)
  le_last : ∀ x ∈ elems, x ≤ last
  last_mem : last ∈ elems

private lemma exists_next_sidon (st : SidonState) :
    ∃ x : ℕ, st.last < x ∧ IsSidonSet (insert x (st.elems : Set ℕ)) :=
  ⟨2 * st.last + 1, by omega,
    isSidonSet_insert_of_gt_two_mul st.sidon
      (fun s hs => st.le_last s (Finset.mem_coe.mp hs)) (by omega)⟩

private def mcInit : SidonState where
  last := 1
  elems := {1}
  sidon := by
    intro u hu v hv z hz w hw _ _ _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv hz hw
    omega
  le_last := by
    intro x hx
    simp only [mem_singleton] at hx
    omega
  last_mem := mem_singleton_self 1

open Classical in
private noncomputable def mcNextVal (st : SidonState) : ℕ :=
  Nat.find (exists_next_sidon st)

open Classical in
private lemma mcNextVal_spec (st : SidonState) :
    st.last < mcNextVal st ∧ IsSidonSet (insert (mcNextVal st) (st.elems : Set ℕ)) :=
  Nat.find_spec (exists_next_sidon st)

open Classical in
private lemma mcNextVal_min (st : SidonState) {y : ℕ} (hy : y < mcNextVal st) :
    ¬ (st.last < y ∧ IsSidonSet (insert y (st.elems : Set ℕ))) :=
  Nat.find_min (exists_next_sidon st) hy

private noncomputable def mcNext (st : SidonState) : SidonState where
  last := mcNextVal st
  elems := insert (mcNextVal st) st.elems
  sidon := by
    rw [Finset.coe_insert]
    exact (mcNextVal_spec st).2
  le_last := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy'
    · exact le_rfl
    · exact le_trans (st.le_last y hy') (le_of_lt (mcNextVal_spec st).1)
  last_mem := mem_insert_self (mcNextVal st) st.elems

private noncomputable def mcState : ℕ → SidonState
  | 0 => mcInit
  | n + 1 => mcNext (mcState n)

/-- The classical Mian–Chowla greedy Sidon sequence (`1, 2, 4, 8, 13, 21, ...`),
0-indexed so that `mianChowla 0 = 1`. -/
noncomputable def mianChowla (n : ℕ) : ℕ := (mcState n).last

lemma mianChowla_zero : mianChowla 0 = 1 := rfl

lemma mianChowla_strictMono : StrictMono mianChowla :=
  strictMono_nat_of_lt_succ (fun n => (mcNextVal_spec (mcState n)).1)

private lemma mcState_elems (n : ℕ) :
    (mcState n).elems = (range (n + 1)).image mianChowla := by
  induction n with
  | zero =>
    simp [mcState, mcInit, mianChowla]
  | succ n ih =>
    change insert (mianChowla (n + 1)) (mcState n).elems =
      (range (n + 2)).image mianChowla
    rw [ih]
    have hr : range (n + 2) = insert (n + 1) (range (n + 1)) := Finset.range_add_one
    rw [hr, Finset.image_insert]

theorem mianChowla_isGreedySidon : IsGreedySidonFrom mianChowla 0 where
  strictMono := mianChowla_strictMono
  prefix_sidon := fun m _ => by
    rw [← mcState_elems m]
    exact (mcState m).sidon
  greedy_min := fun m y _ h1 h2 => by
    rw [← mcState_elems m]
    intro hsid
    exact mcNextVal_min (mcState m) h2 ⟨h1, hsid⟩

lemma mianChowla_one : mianChowla 1 = 2 := by
  have hge : 2 ≤ mianChowla 1 := by
    have := mianChowla_strictMono (by omega : 0 < 1)
    rw [mianChowla_zero] at this
    omega
  by_contra hne
  have hlt : 2 < mianChowla 1 := by omega
  have hnot :=
    mianChowla_isGreedySidon.greedy_min 0 2 le_rfl (by rw [mianChowla_zero]; omega) hlt
  have hset : (((range (0 + 1)).image mianChowla : Finset ℕ) : Set ℕ) = {1} := by
    simp [mianChowla_zero]
  rw [hset] at hnot
  apply hnot
  intro u hu v hv z hz w hw huv hzw heq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv hz hw
  omega

/-- The classical Mian–Chowla sequence is a Sidon set (`B₂`-set). -/
theorem mianChowla_isSidon : IsSidonSet (Set.range mianChowla) := by
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ z ⟨k, rfl⟩ w ⟨l, rfl⟩ huv hzw heq
  let m := max (max i j) (max k l)
  have hmem : ∀ t, t ≤ m → mianChowla t ∈ ((mcState m).elems : Set ℕ) := by
    intro t ht
    rw [mcState_elems m, Finset.mem_coe]
    exact mem_image.mpr ⟨t, mem_range.mpr (by omega), rfl⟩
  exact (mcState m).sidon
    _ (hmem i (by omega)) _ (hmem j (by omega))
    _ (hmem k (by omega)) _ (hmem l (by omega))
    huv hzw heq

/-- Main corollary for the classical Mian–Chowla sequence:
eventually `mianChowla n / n^3 ≤ 1/6 - 1/12000000`. -/
theorem mianChowla_eventually_le_below_one_sixth :
    ∀ᶠ n : ℕ in atTop, (mianChowla n : ℝ) / (n : ℝ) ^ 3 ≤ 1 / 6 - 1 / 12000000 :=
  greedySidon_eventually_le_below_one_sixth mianChowla_isGreedySidon

#print axioms greedySidon_eventually_le_below_one_sixth
#print axioms mianChowla_eventually_le_below_one_sixth

end MianChowla
