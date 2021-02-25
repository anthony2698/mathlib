/-
Copyright (c) 2021 Hanting Zhang. No rights reserved.
Authors: None
-/
import analysis.special_functions.pow
import measure_theory.interval_integral
import data.nat.parity

namespace real

open filter set finset interval_integral measure_theory
open_locale real classical big_operators topological_space
local notation `|`x`|` := abs x

/-! ### Wallis Product for Pi -/
-- if `f : ℝ → ℝ` is integrable on `[a, b]`, then the function restriction
-- `f : [a, b] → ℝ` is integrable on `[a, b]`, treating `[a, b]` as a measurable space.
noncomputable def integral_sin_nth (n : ℕ) := ∫ x in (0:ℝ)..π, (sin x)^n

lemma interval_integral.mul_const {a b : ℝ} {f : ℝ → ℝ} (c : ℝ) :
  ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
by simp only [interval_integral, mul_sub, ← measure_theory.integral_mul_left]

lemma ratio (n : ℕ) : integral_sin_nth (n + 2) = (n + 1) / (n + 2) * integral_sin_nth n :=
begin
  have h : integral_sin_nth (n + 2) =
    ((↑n + 1) * ∫ (x : ℝ) in 0..π, sin x ^ n) - (↑n + 1) * ∫ (x : ℝ) in 0..π, sin x ^ (n + 2) :=
begin
  unfold integral_sin_nth,
  have h₁ : (λ x, (sin x)^(n + 2)) = λ x, (sin x)^(n + 1) * sin x :=
    by simp [pow_succ, mul_assoc, mul_comm],

  conv_lhs { rw h₁, },
  rw @integral_mul_deriv_eq_deriv_mul 0 π _ (λ x, -cos x) (λ x, cos x * (n + 1) * sin x ^ n) _,
  { simp only [neg_mul_eq_neg_mul_symm, sin_zero, sin_pi, zero_mul, sub_zero,
      add_eq_zero_iff, ne.def, zero_add, not_false_iff, one_ne_zero, interval_integral.integral_neg,
      and_false, zero_pow', sub_neg_eq_add],
    have h₂ : (λ x, cos x * (cos x * (n + 1) * sin x ^ n)) =
        (λ x, (n + 1) * (cos x ^ 2 * sin x ^ n)) :=
      by { funext, ring },
    rw h₂,
    simp only [cos_square', sub_mul, mul_sub, one_mul, ← pow_add _ 2 n, add_comm 2 n],
    rw interval_integral.integral_sub,
    -- generalize
    simp only [interval_integral.mul_const ((n:ℝ) + 1)],
    exact ((@continuous_const _ _ _ _ ((n:ℝ) + 1)).mul
      ((continuous_pow n).comp continuous_sin)).interval_integrable 0 π,
    exact (continuous.interval_integrable (continuous.mul (@continuous_const _ _ _ _ ((n:ℝ) + 1))
      (continuous.comp (continuous_pow (n + 2)) continuous_sin))) 0 π, },
  { intros,
    have := has_deriv_at.comp x (has_deriv_at_pow (n + 1) (sin x)) (has_deriv_at_sin x),
    convert this using 1,
    simp only [nat.add_succ_sub_one, add_zero, nat.cast_add, nat.cast_one],
    rw [mul_assoc, mul_comm], },
  { intros,
    have h := has_deriv_at.neg (has_deriv_at_cos x),
    rw neg_neg at h,
    exact h, },
  { apply continuous.continuous_on,
    continuity,
    exact continuous_cos,
    exact continuous_sin, },
  { exact real.continuous_sin.continuous_on, }
end,
  rw [eq_sub_iff_add_eq, ← one_mul (integral_sin_nth (n + 2)), integral_sin_nth, ← add_mul,
    ← add_assoc, add_comm (1:ℝ) n, add_assoc] at h,
  field_simp,
  rw [integral_sin_nth, integral_sin_nth, ← h, eq_div_iff_mul_eq, mul_comm],
  refl,
  norm_cast,
  norm_num,
end

theorem integral_sin_nth_odd (n : ℕ) :
  integral_sin_nth (2 * n + 1) = 2 * ∏ i in range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih,
  { have h : sin = deriv (λ x : ℝ, -cos x) , by simp,
    simp only [integral_sin_nth, mul_one, range_zero, pow_one, finset.prod_empty, mul_zero, h],
    rw integral_deriv_eq_sub,
    { simp, ring },
    { simp },
    { rw  ← h,
      exact continuous_sin.continuous_on } },
  rw [prod_range_succ, ← mul_assoc, mul_comm (2:ℝ) ((2 * k + 2) / (2 * k + 3)), mul_assoc, ← ih],
  have h₁ : 2 * k.succ + 1 = 2 * k + 1 + 2 :=
  by { rw nat.succ_eq_add_one k, rw mul_add, rw mul_one, },
  have h₂ : (2:ℝ) * k + 1 + 1 = 2 * k + 2 := by { norm_cast, },
  have h₃ : (2:ℝ) * k + 1 + 2 = 2 * k + 3 := by { norm_cast, },
  rw [h₁, ratio (2 * k + 1)],
  simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul, h₂, h₃],
end

theorem integral_sin_nth_even (n : ℕ) :
  integral_sin_nth (2 * n) = π * ∏ i in range n, (2 * i + 1) / (2 * i + 2) :=
begin
  induction n with k ih,
  { simp [integral_sin_nth, interval_integral.integral_const] },
  rw [prod_range_succ, ← mul_assoc, mul_comm π ((2 * k + 1) / (2 * k + 2)), mul_assoc, ← ih],
  simp [nat.succ_eq_add_one, mul_add, mul_one, ratio _],
end

lemma cancel (a b : ℝ) (h : a / b ≠ 0) : a / b * (b / a) = 1 :=
begin
  rw ← @inv_div _ _ a b,
  exact mul_inv_cancel h,
end

lemma interval_integral.integral_mono {a b : ℝ} {f g : ℝ → ℝ}
  {hf : integrable f (volume.restrict (Ioc a b))}
  {hg : integrable g (volume.restrict (Ioc a b))} (h : a ≤ b) :
  (∀ x, x ∈ Ioc a b → f x ≤ g x) → ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
begin
  intro hx,
  rw [integral_of_le h, integral_of_le h],
  refine integral_mono_ae hf hg (eventually_of_mem _ hx),
  simp only [mem_ae_iff, measure.restrict_apply (measurable_set.compl measurable_set_Ioc),
    set.compl_inter_self, measure_empty],
end

lemma integral_sin_pow_anti_mono (n : ℕ) :
  ∫ (x : ℝ) in 0..π, sin x ^ (n + 1) ≤ ∫ (x : ℝ) in 0..π, sin x ^ n :=
begin
  apply interval_integral.integral_mono,
  exact (((continuous_pow (n + 1)).comp continuous_sin).interval_integrable 0 π).1.integrable,
  exact (((continuous_pow n).comp continuous_sin).interval_integrable 0 π).1.integrable,
  exact pi_pos.le,
  intros x hx,
  calc sin x ^ (n + 1) ≤ sin x ^ n * 1 :
    by { rw pow_add, rw pow_one, refine mul_le_mul_of_nonneg_left (sin_le_one x) _,
      exact (pow_nonneg (sin_nonneg_of_mem_Icc (mem_Icc_of_Ioc hx)) n), }
  ... = sin x ^ n : by { rw mul_one }
end

lemma integral_pos {a b : ℝ}  {f : ℝ → ℝ} (h : a ≤ b) :
  (∀ x, x ∈ Ioc a b → 0 < f x) → 0 < ∫ x in a..b, f x :=
begin
  intros hx,

  sorry
end

/-- generalize, make shorter -/
lemma integral_sin_nth_pos (n : ℕ) : 0 < integral_sin_nth n :=
begin
  rcases nat.even_or_odd' n with ⟨k, h, h⟩,
  rw h,
  rw integral_sin_nth_even,
  refine mul_pos pi_pos _,
  apply prod_pos,
  intros,
  apply div_pos,
  norm_cast, linarith,
  norm_cast, linarith,
  rw h,
  rw integral_sin_nth_odd,
  refine mul_pos (by norm_num) _,
  apply prod_pos,
  intros,
  apply div_pos,
  norm_cast, linarith,
  norm_cast, linarith,
end

lemma ratio_tendsto_one :
  tendsto (λ (k : ℕ), integral_sin_nth (2 * k + 1) / integral_sin_nth (2 * k)) at_top (𝓝 1) :=
begin
  have h₃ : ∀ n, integral_sin_nth (2 * n + 1) / integral_sin_nth (2 * n) ≤ 1 :=
  begin
    intro,
    rw div_le_one (integral_sin_nth_pos _),
    exact integral_sin_pow_anti_mono _,
  end,
  have h₄ : ∀ n, integral_sin_nth (2 * n + 1) / integral_sin_nth (2 * n) ≥ 2 * n / (2 * n + 1) :=
  begin
    intro,
    rw ge_iff_le,
    calc 2 * ↑n / (2 * ↑n + 1)
        ≤ integral_sin_nth (2 * n + 1) / integral_sin_nth (2 * n - 1) :
    begin
      cases n,
      simp only [div_nonneg (integral_sin_nth_pos 1).le (integral_sin_nth_pos 0).le,
        zero_div, nat.cast_zero, mul_zero],
      rw le_div_iff (integral_sin_nth_pos _),
      apply le_of_eq,
      convert eq.symm (ratio (2 * n + 1)) using 2,
      simp only [mul_add, mul_one, nat.cast_succ, nat.cast_add, nat.cast_one,
        nat.cast_mul, add_assoc, add_comm (1:ℝ) 2],
      refl,
    end
    ... ≤ integral_sin_nth (2 * n + 1) / integral_sin_nth (2 * n) :
    begin
      rw div_le_div_left (integral_sin_nth_pos _) (integral_sin_nth_pos _) (integral_sin_nth_pos _),
      cases n, simp only [mul_zero],
      exact integral_sin_pow_anti_mono _,
    end,
  end,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ _ _,
  exact λ n, 2 * n / (2 * n + 1),
  exact λ n, 1,

  -- any way to make this faster?

  rw [tendsto_iff_norm_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero],
  have h : (λ (e : ℕ), (2:ℝ) * e / (2 * e + 1) - 1) = λ (e : ℕ), -1 / (2 * e + 1) :=
  begin
    funext,
    conv_lhs { congr, skip, rw ← @div_self _ _ ((2:ℝ) * e + 1) (by { norm_cast, linarith }), },
    rw [← sub_div, ← sub_sub, sub_self, zero_sub],
  end,
  rw h,
  simp only [neg_div, one_div],
  rw ← neg_zero,
  apply filter.tendsto.neg,
  apply tendsto.inv_tendsto_at_top,
  refine tendsto.at_top_add _ tendsto_const_nhds,
  refine tendsto.mul_at_top (zero_lt_two) tendsto_const_nhds _,
  rw tendsto_at_top,
  intros b,
  simp only [ge_iff_le, eventually_at_top],
  use int.to_nat (ceil b),
  intros,
  calc b ≤ ceil b : by {exact le_ceil b}
  ... ≤ (ceil b).to_nat : begin norm_cast, exact int.le_to_nat (ceil b), end
  ... ≤ b_1 : by { norm_cast, exact H, },
  exact tendsto_const_nhds,
  exact λ n, (h₄ n).le,
  exact λ n, (h₃ n),
end

/-- refactor constant multiplication? -/
theorem tendsto_prod_pi_div_two :
  tendsto (λ k, ∏ i in range k,
    (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) at_top (𝓝 (π/2)) :=
begin
  suffices h : tendsto (λ k, 2 / π  * ∏ i in range k,
    (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) at_top (𝓝 1),
  have := tendsto.const_mul (π / 2) h,
  simp only [← mul_assoc, cancel π 2 (by { norm_num, exact pi_ne_zero }), one_mul, mul_one] at this,
  exact this,
  have h : (λ (k : ℕ), (2:ℝ) / π * ∏ (i : ℕ) in range k,
    ((2 * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3))) =
  λ k, (2 * ∏ i in range k,
    (2 * i + 2) / (2 * i + 3)) / (π * ∏ (i : ℕ) in range k, (2 * i + 1) / (2 * i + 2)) :=
  begin
    funext,
    rw prod_mul_distrib,
    have bonk : ∏ (i : ℕ) in range k, ((2:ℝ) * ↑i + 2) / (2 * ↑i + 1) =
      1 / (∏ (i : ℕ) in range k, (2 * ↑i + 1) / (2 * ↑i + 2)) :=
    begin
      rw eq_div_iff_mul_eq,
      rw ← prod_mul_distrib,
      apply prod_eq_one,
      intros,
      field_simp,
      rw mul_comm,
      rw div_self,
      norm_cast,
      apply nat.mul_ne_zero,
      linarith, linarith,
      rw prod_ne_zero_iff,
      intros,
      apply div_ne_zero,
      norm_cast, linarith,
      norm_cast, linarith,
    end,
    rw bonk,
    field_simp,
  end,
  rw h,
  simp only [← integral_sin_nth_even, ← integral_sin_nth_odd],
  exact ratio_tendsto_one,
end

end real
