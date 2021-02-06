import analysis.calculus.local_extr
import analysis.calculus.implicit

open filter set
open_locale topological_space filter big_operators
variables {E F : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
  {f : E → F} {φ : E → ℝ} {x₀ : E} {f' : E →L[ℝ] F} {φ' : E →L[ℝ] ℝ}

lemma is_local_extr_on.range_ne_top_of_has_strict_fderiv_at
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  (f'.prod φ').range ≠ ⊤ :=
begin
  intro htop,
  set fφ := λ x, (f x, φ x),
  have A : map φ (𝓝[f ⁻¹' {f x₀}] x₀) = 𝓝 (φ x₀),
  { change map (prod.snd ∘ fφ) (𝓝[fφ ⁻¹' {p | p.1 = f x₀}] x₀) = 𝓝 (φ x₀),
    rw [← map_map, nhds_within, map_inf_principal_preimage, (hf'.prod hφ').map_nhds_eq htop],
    exact map_snd_nhds_within _ },
  exact hextr.not_nhds_le_map A.ge
end

lemma is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : F →L[ℝ] ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, Λ (f' x) + Λ₀ * φ' x = 0 :=
begin
  rcases submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.2 $ hextr.range_ne_top_of_has_strict_fderiv_at hf' hφ') with ⟨Λ', h0, hΛ'⟩,
  refine ⟨(Λ'.comp (linear_map.inl _ _ _)).to_continuous_linear_map, Λ' (0, 1), _, _⟩,
  { contrapose! h0,
    simp only [linear_equiv.map_eq_zero_iff, prod.mk_eq_zero] at h0,
    ext ⟨x, c⟩,
    calc Λ' (x, c) = Λ' ((x, 0) + (0, c)) : by simp
    ... = (Λ'.comp (linear_map.inl ℝ F ℝ)) x + Λ' (0, c) : Λ'.map_add _ _
    ... = Λ' (0, c) : by rw [h0.1, linear_map.zero_apply, zero_add]
    ... = c • Λ' (0, 1) : by { rw [← Λ'.map_smul], simp }
    ... = 0 : by rw [h0.2, smul_zero] },
  { intro x,
    suffices : Λ' (f' x, 0) + Λ' (0, 1) * φ' x = 0, by simpa,
    rw [mul_comm, ← smul_eq_mul, ← Λ'.map_smul, ← Λ'.map_add],
    suffices : (f' x, φ' x) ∈ Λ'.ker, by simpa,
    exact hΛ' (linear_map.mem_range_self _ _) }
end

lemma is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at {ι : Type*} [fintype ι]
  {f : ι → E → ℝ} {f' : ι → E →L[ℝ] ℝ}
  (hextr : is_local_extr_on φ {x | ∀ i, f i x = f i x₀} x₀)
  (hf' : ∀ i, has_strict_fderiv_at (f i) (f' i) x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, (∑ i, Λ i * f' i x) + Λ₀ * φ' x = 0 :=
begin
  classical,
  replace hextr : is_local_extr_on φ {x | (λ i, f i x) = (λ i, f i x₀)} x₀,
    by simpa only [function.funext_iff] using hextr,
  rcases hextr.exists_linear_map_of_has_strict_fderiv_at
    (has_strict_fderiv_at.pi (λ i, hf' i)) hφ'
    with ⟨Λ, Λ₀, h0, hsum⟩,
  refine ⟨λ i, Λ (pi.single i 0), Λ₀, _, _⟩,
  { contrapose! h0,
    simp only [prod.mk_eq_zero, pi.single] at h0 ⊢, refine ⟨_, h0.2⟩,
    ext x,
    rw [continuous_linear_map.zero_apply, pi_eq_sum_univ x],  }
end
