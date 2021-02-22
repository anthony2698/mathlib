import analysis.calculus.local_extr
import analysis.calculus.implicit

open filter set
open_locale topological_space filter big_operators
variables {E F : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  [normed_group F] [normed_space ℝ F] [complete_space F]
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
    rw [← map_map, nhds_within, map_inf_principal_preimage,
      (hf'.prod hφ').map_nhds_eq_of_surj htop],
    exact map_snd_nhds_within _ },
  exact hextr.not_nhds_le_map A.ge
end

lemma is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at
  (hextr : is_local_extr_on φ {x | f x = f x₀} x₀) (hf' : has_strict_fderiv_at f f' x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : F →ₗ[ℝ] ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ Λ.comp (f' : E →ₗ[ℝ] F) + Λ₀ • φ' = 0 :=
begin
  rcases submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.2 $ hextr.range_ne_top_of_has_strict_fderiv_at hf' hφ') with ⟨Λ', h0, hΛ'⟩,
  set e : ((F →ₗ[ℝ] ℝ) × ℝ) ≃ₗ[ℝ] (F × ℝ →ₗ[ℝ] ℝ) :=
    ((linear_equiv.refl ℝ (F →ₗ[ℝ] ℝ)).prod (linear_map.ring_lmap_equiv_self ℝ ℝ ℝ).symm).trans
      (linear_map.coprod_equiv ℝ),
  rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩,
  refine ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, _⟩,
  convert linear_map.range_le_ker_iff.1 hΛ',
  ext x,
  -- squeezed `simp [mul_comm]` to speed up elaboration
  simp only [linear_map.coprod_equiv_apply, linear_equiv.refl_apply, linear_map.one_app,
    linear_equiv.trans_apply, smul_eq_mul, linear_equiv.prod_apply, linear_map.smul_apply,
    linear_map.coprod_comp_prod, linear_map.smul_right_apply,
    linear_map.ring_lmap_equiv_self_symm_apply, continuous_linear_map.coe_prod, mul_comm,
    continuous_linear_map.coe_coe, linear_map.add_apply, linear_map.comp_apply]
end

lemma is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at {ι : Type*} [fintype ι]
  {f : ι → E → ℝ} {f' : ι → E →L[ℝ] ℝ}
  (hextr : is_local_extr_on φ {x | ∀ i, f i x = f i x₀} x₀)
  (hf' : ∀ i, has_strict_fderiv_at (f i) (f' i) x₀)
  (hφ' : has_strict_fderiv_at φ φ' x₀) :
  ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∑ i, Λ i • f' i + Λ₀ • φ' = 0 :=
begin
  letI := classical.dec_eq ι,
  replace hextr : is_local_extr_on φ {x | (λ i, f i x) = (λ i, f i x₀)} x₀,
    by simpa only [function.funext_iff] using hextr,
  rcases hextr.exists_linear_map_of_has_strict_fderiv_at
    (has_strict_fderiv_at_pi.2 (λ i, hf' i)) hφ'
    with ⟨Λ, Λ₀, h0, hsum⟩,
  rw [continuous_linear_map.coe_pi] at hsum,
  rcases (linear_equiv.pi_dual ι ℝ).symm.surjective Λ with ⟨Λ, rfl⟩,
  refine ⟨Λ, Λ₀, _, _⟩,
  { simpa only [ne.def, prod.ext_iff, linear_equiv.map_eq_zero_iff, prod.fst_zero] using h0 },
  { ext x,
    simpa using linear_map.congr_fun hsum x }
end
