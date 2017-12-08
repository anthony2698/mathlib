/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type of functions with finite support.

Functions with finite support provide the basis for the following concrete instances:

 * ℕ →₀ α: Polynomials (where α is a ring)
 * (σ →₀ ℕ) →₀ α: Multivariate Polynomials (again α is a ring, and σ are variable names)
 * α →₀ ℕ: Multisets
 * α →₀ ℤ: Abelean groups freely generated by α
 * β →₀ α: Linear combinations over β where α is the scalar ring

Most of the theory assumes that the range is a commutative monoid. This gives us the big sum
operator as a powerful way to construct `finsupp` elements.

A general adivice is to not use α →₀ β directly, as the type class setup might not be fitting.
The best is to define a copy and select the instances best suited.

-/

import data.set.finite data.finset algebra.big_operators
noncomputable theory

open classical set function
local attribute [instance] decidable_inhabited prop_decidable

reserve infix ` →₀ `:25

universes u u₁ u₂ v v₁ v₂ v₃ w x y

/- Should we use finset instead of finite? -/

def finsupp (α : Type u) (β : Type v) [has_zero β] := {f : α → β // finite {a | f a ≠ 0}}

infix →₀ := finsupp

namespace finsupp
variables {α : Type u} {β : Type v} {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}

section
variable [has_zero β]

instance : has_coe_to_fun (α →₀ β) := ⟨λ_, α → β, subtype.val⟩

instance : has_zero (α →₀ β) := ⟨⟨(λ_, 0), by simp [finite_empty]⟩⟩
@[simp] lemma zero_apply {a : α} : (0 : α →₀ β) a = 0 := rfl

instance : inhabited (α →₀ β) := ⟨0⟩

lemma ext : ∀{f g : α →₀ β}, (∀a, f a = g a) → f = g
| ⟨f, _⟩ ⟨g, _⟩ h := subtype.eq $ funext $ h

lemma finite_supp (f : α →₀ β) : finite {a | f a ≠ 0} :=
f.property

def support (f : α →₀ β) : finset α := f.finite_supp.to_finset

@[simp] lemma mem_support_iff (f : α →₀ β) {a : α} : a ∈ f.support ↔ f a ≠ 0 :=
by simp [finsupp.support]

@[simp] lemma support_zero : (0 : α →₀ β).support = ∅ :=
by simp [finset.ext]

def single (a : α) (b : β) : α →₀ β :=
⟨λa', if a = a' then b else 0,
  finite_subset (@finite_singleton α a) $ assume a', by by_cases a = a' with h; simp [h]⟩

lemma single_apply {a a' : α} {b : β} :
  (single a b : α →₀ β) a' = (if a = a' then b else 0) :=
rfl

@[simp] lemma single_eq_same {a : α} {b : β} :
  (single a b : α →₀ β) a = b :=
by simp [single_apply]

@[simp] lemma single_eq_of_ne {a a' : α} {b : β} (h : a ≠ a') :
  (single a b : α →₀ β) a' = 0 :=
by simp [single_apply, h]

@[simp] lemma single_zero {a : α} : (single a 0 : α →₀ β) = 0 :=
ext $ assume a',
begin
  by_cases a = a' with h,
  { rw [h, single_eq_same, zero_apply] },
  { rw [single_eq_of_ne h, zero_apply] }
end

lemma support_single_subset {a : α} {b : β} : (single a b).support ⊆ {a} :=
have ∀a', (if a = a' then b else 0) ≠ 0 → a' = a,
  by intro a'; by_cases a = a'; simp [*],
by simpa [finset.subset_iff, mem_support_iff, single_apply] using this

lemma support_single_ne_zero {a : α} {b : β} (hb : b ≠ 0) :
  (single a b).support = {a} :=
finset.subset.antisymm
  support_single_subset
  (finset.subset_iff.mpr $ by simp [mem_support_iff, hb])

end

def map_range [has_zero β₁] [has_zero β₂]
  (f : β₁ → β₂) (hf : f 0 = 0) (g : α →₀ β₁) : α →₀ β₂ :=
⟨f ∘ g, finite_subset g.finite_supp $
  assume a, by simp [(∘), hf, not_imp_not] {contextual:=tt}⟩

@[simp] lemma map_range_apply [has_zero β₁] [has_zero β₂]
  {f : β₁ → β₂} {hf : f 0 = 0} {g : α →₀ β₁} {a : α} : map_range f hf g a = f (g a) :=
rfl

lemma support_map_range [has_zero β₁] [has_zero β₂]
  {f : β₁ → β₂} {hf : f 0 = 0} {g : α →₀ β₁} :
  (map_range f hf g).support ⊆ g.support :=
by simp [finset.subset_iff, not_imp_not, hf] {contextual:=tt}

def zip_with [has_zero β] [has_zero β₁] [has_zero β₂] (f : β₁ → β₂ → β) (hf : f 0 0 = 0)
  (g₁ : α →₀ β₁) (g₂ : α →₀ β₂) : (α →₀ β) :=
⟨λa, f (g₁ a) (g₂ a), finite_subset (finite_union g₁.finite_supp g₂.finite_supp) $
  assume a hfa, not_and_distrib.mp $ assume ⟨ha₁, ha₂⟩, hfa $ by simp [ha₁, ha₂, hf]⟩

@[simp] lemma zip_with_apply [has_zero β] [has_zero β₁] [has_zero β₂]
  {f : β₁ → β₂ → β} {hf : f 0 0 = 0} {g₁ : α →₀ β₁} {g₂ : α →₀ β₂} {a : α} :
  zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
rfl

lemma support_zip_with [has_zero β] [has_zero β₁] [has_zero β₂]
  {f : β₁ → β₂ → β} {hf : f 0 0 = 0} {g₁ : α →₀ β₁} {g₂ : α →₀ β₂} :
  (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
begin
  simp [finset.subset_iff, finset.mem_union, mem_support_iff],
  intro x,
  rw [←not_and_distrib, not_imp_not],
  simp [hf] {contextual := tt}
end

def sum {γ : Type w} [has_zero β] [add_comm_monoid γ] (f : α →₀ β) (g : α → β → γ) : γ :=
f.support.sum (λa, g a (f a))

lemma sum_map_range_index {γ : Type w} [has_zero β₁] [has_zero β₂] [add_comm_monoid γ]
  {f : β₁ → β₂} {hf : f 0 = 0} {g : α →₀ β₁} {h : α → β₂ → γ} (h0 : ∀a, h a 0 = 0) :
  (map_range f hf g).sum h = g.sum (λa b, h a (f b)) :=
finset.sum_subset support_map_range $ by simp [h0] {contextual := tt}

lemma sum_zero_index {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {h : α → β → γ} :
  (0 : α →₀ β).sum h = 0 :=
by simp [finsupp.sum, support_zero]

lemma sum_single_index {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {a : α} {b : β}
  {h : α → β → γ} (h_zero : h a 0 = 0) : (single a b).sum h = h a b :=
begin
  by_cases b = 0 with h,
  { simp [h, sum_zero_index, h_zero] },
  { simp [finsupp.sum, support_single_ne_zero h] }
end

instance [add_monoid β] : has_add (α →₀ β) :=
⟨zip_with (+) (add_zero 0)⟩

@[simp] lemma add_apply [add_monoid β] {g₁ g₂ : α →₀ β} {a : α} :
  (g₁ + g₂) a = g₁ a + g₂ a :=
rfl

lemma support_add [add_monoid β] {g₁ g₂ : α →₀ β} :
  (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

@[simp] lemma single_add [add_monoid β] {a : α} {b₁ b₂ : β} :
  single a (b₁ + b₂) = single a b₁ + single a b₂ :=
ext $ assume a',
begin
  by_cases a = a' with h,
  { rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add] }
end

instance [add_monoid β] : add_monoid (α →₀ β) :=
{ add_monoid .
  zero      := 0,
  add       := (+),
  add_assoc := assume ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩, ext $ assume a, add_assoc _ _ _,
  zero_add  := assume ⟨f, hf⟩, ext $ assume a, zero_add _,
  add_zero  := assume ⟨f, hf⟩, ext $ assume a, add_zero _ }

instance [add_comm_monoid β] : add_comm_monoid (α →₀ β) :=
{ add_comm := assume ⟨f, _⟩ ⟨g, _⟩, ext $ assume a, add_comm _ _,
  .. finsupp.add_monoid }

instance [add_group β] : add_group (α →₀ β) :=
{ neg          := map_range (has_neg.neg) neg_zero,
  add_left_neg := assume ⟨f, _⟩, ext $ assume x, add_left_neg _,
  .. finsupp.add_monoid }

lemma sum_neg_index {γ : Type w} [add_group β] [add_comm_monoid γ]
  {g : α →₀ β} {h : α → β → γ} (h0 : ∀a, h a 0 = 0) :
  (-g).sum h = g.sum (λa b, h a (- b)) :=
sum_map_range_index h0

@[simp] lemma neg_apply [add_group β] {g : α →₀ β} {a : α} :
  (- g) a = - g a :=
rfl

@[simp] lemma sub_apply [add_group β] {g₁ g₂ : α →₀ β} {a : α} :
  (g₁ - g₂) a = g₁ a - g₂ a :=
rfl

instance [add_comm_group β] : add_comm_group (α →₀ β) :=
{ add_comm := add_comm, ..finsupp.add_group }

@[simp] lemma sum_apply [has_zero β] [add_comm_monoid β₁]
  {f : α₁ →₀ β} {g : α₁ → β → α₂ →₀ β₁} {a₂ : α₂} :
  (f.sum g) a₂ = f.sum (λa₁ b, g a₁ b a₂) :=
(finset.sum_hom (λf : α₂ →₀ β₁, f a₂) rfl (assume a b, rfl)).symm

lemma support_sum [has_zero β] [add_comm_monoid β₁]
  {f : α →₀ β} {g : α → β → (α₁ →₀ β₁)} :
  (f.sum g).support ⊆ f.support.bind (λa, (g a (f a)).support) :=
have ∀a₁ : α₁, f.sum (λ (a : α) (b : β), (g a b) a₁) ≠ 0 →
    (∃ (a : α), f a ≠ 0 ∧ ¬ (g a (f a)) a₁ = 0),
  from assume a₁ h,
  let ⟨a, ha, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨a, f.mem_support_iff.mp ha, ne⟩,
by simpa [finset.subset_iff, mem_support_iff, finset.mem_bind, sum_apply] using this

@[simp] lemma sum_zero {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {f : α →₀ β} :
  f.sum (λa b, (0 : γ)) = 0 :=
finset.sum_const_zero

@[simp] lemma sum_add {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {f : α →₀ β}
  {h₁ h₂ : α → β → γ} :
  f.sum (λa b, h₁ a b + h₂ a b) = f.sum h₁ + f.sum h₂ :=
finset.sum_add_distrib

@[simp] lemma sum_neg {γ : Type w} [add_comm_monoid β] [add_comm_group γ] {f : α →₀ β}
  {h : α → β → γ} : f.sum (λa b, - h a b) = - f.sum h :=
finset.sum_hom (@has_neg.neg γ _) neg_zero (assume a b, neg_add _ _)

@[simp] lemma sum_single [add_comm_monoid β] {f : α →₀ β} :
  f.sum single = f :=
have ∀a:α, f.sum (λa' b, ite (a' = a) b 0) =
    ({a} : finset α).sum (λa', ite (a' = a) (f a') 0),
begin
  intro a,
  by_cases a ∈ f.support with h,
  { have : {a} ⊆ f.support,
      { simp [finset.subset_iff, *] at * },
    refine (finset.sum_subset this _).symm,
    simp {contextual := tt} },
  { transitivity (f.support.sum (λa, (0 : β))),
    { refine (finset.sum_congr _),
      intros a' ha',
      have h: a' ≠ a,
        { assume eq, simp * at * },
      simp * at * },
    { simp * at * } }
end,
ext $ assume a, by simp [single_apply, this]

lemma sum_add_index {γ : Type w} [add_comm_monoid β] [add_comm_monoid γ] {f g : α →₀ β}
  {h : α → β → γ} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (f + g).sum h = f.sum h + g.sum h :=
have f_eq : (f.support ∪ g.support).sum (λa, h a (f a)) = f.sum h,
  from (finset.sum_subset finset.subset_union_left $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
have g_eq : (f.support ∪ g.support).sum (λa, h a (g a)) = g.sum h,
  from (finset.sum_subset finset.subset_union_right $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
calc (f + g).support.sum (λa, h a ((f + g) a)) =
      (f.support ∪ g.support).sum (λa, h a ((f + g) a)) :
    finset.sum_subset support_add $
      by simp [mem_support_iff, h_zero] {contextual := tt}
  ... = (f.support ∪ g.support).sum (λa, h a (f a)) +
      (f.support ∪ g.support).sum (λa, h a (g a)) :
    by simp [h_add, finset.sum_add_distrib]
  ... = _ : by rw [f_eq, g_eq]

lemma sum_sub_index {γ : Type w} [add_comm_group β] [add_comm_group γ] {f g : α →₀ β}
  {h : α → β → γ} (h_sub : ∀a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
have h_zero : ∀a, h a 0 = 0,
  from assume a,
  have h a (0 - 0) = h a 0 - h a 0, from h_sub a 0 0,
  by simpa using this,
have h_neg : ∀a b, h a (- b) = - h a b,
  from assume a b,
  have h a (0 - b) = h a 0 - h a b, from h_sub a 0 b,
  by simpa [h_zero] using this,
have h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂,
  from assume a b₁ b₂,
  have h a (b₁ - (- b₂)) = h a b₁ - h a (- b₂), from h_sub a b₁ (-b₂),
  by simpa [h_neg] using this,
calc (f - g).sum h = (f + - g).sum h : by simp
  ... = f.sum h + - g.sum h : by simp [sum_add_index, sum_neg_index, h_add, h_zero, h_neg]
  ... = _ : by simp

lemma sum_finset_sum_index {γ : Type w} {ι : Type x} [add_comm_monoid β] [add_comm_monoid γ]
  {s : finset ι} {g : ι → α →₀ β}
  {h : α → β → γ} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂):
  s.sum (λi, (g i).sum h) = (s.sum g).sum h :=
finset.sum_hom (λf : α →₀ β, f.sum h) sum_zero_index (assume f g, sum_add_index h_zero h_add)

lemma sum_sum_index {γ : Type w} [add_comm_monoid β₁] [add_comm_monoid β₂] [add_comm_monoid γ]
  {f : α₁ →₀ β₁} {g : α₁ → β₁ → α₂ →₀ β₂}
  {h : α₂ → β₂ → γ} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂):
  (f.sum g).sum h = f.sum (λa b, (g a b).sum h) :=
(sum_finset_sum_index h_zero h_add).symm

section map_domain
variables [add_comm_monoid β] {v v₁ v₂ : α →₀ β}

def map_domain (f : α₁ → α₂) (v : α₁ →₀ β) : α₂ →₀ β :=
v.sum $ λa b, single (f a) b

lemma map_domain_id : map_domain id v = v :=
sum_single

lemma map_domain_comp {f : α → α₁} {g : α₁ → α₂} :
  map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
by simp [map_domain, sum_sum_index, sum_single_index]

lemma map_domain_single {f : α → α₁} {a : α} {b : β} : map_domain f (single a b) = single (f a) b :=
sum_single_index (by simp)

lemma map_domain_zero {f : α → α₂} : map_domain f 0 = (0 : α₂ →₀ β) :=
sum_zero_index

lemma map_domain_congr {f g : α → α₂} (h : ∀x∈v.support, f x = g x) :
  v.map_domain f = v.map_domain g :=
finset.sum_congr $ by simp [*] at * { contextual := tt}

lemma map_domain_add {f : α → α₂} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
sum_add_index (by simp) (by simp)

lemma map_domain_finset_sum {ι : Type x} {f : α → α₂} {s : finset ι} {v : ι → α →₀ β} :
  map_domain f (s.sum v) = s.sum (λi, map_domain f (v i)) :=
by refine (sum_finset_sum_index _ _).symm; simp

lemma map_domain_sum [has_zero β₁] {f : α → α₂} {s : α →₀ β₁} {v : α → β₁ → α →₀ β} :
  map_domain f (s.sum v) = s.sum (λa b, map_domain f (v a b)) :=
by refine (sum_finset_sum_index _ _).symm; simp

lemma map_domain_support {f : α → α₂} {s : α →₀ β} :
  (s.map_domain f).support ⊆ s.support.image f :=
finset.subset.trans support_sum $
  finset.subset.trans (finset.bind_mono $ assume a ha, support_single_subset) $
  by rw [finset.bind_singleton]; exact subset.refl _

lemma sum_map_domain_index {γ : Type w} [add_comm_monoid γ] {f : α → α₂} {s : α →₀ β}
  {h : α₂ → β → γ} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (s.map_domain f).sum h = s.sum (λa b, h (f a) b) :=
by simp [map_domain, sum_sum_index, h_zero, h_add, sum_single_index]

end map_domain

instance [has_add α] [semiring β] : has_mul (α →₀ β) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)⟩

lemma mul_def [has_add α] [semiring β] {f g : α →₀ β} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)) :=
rfl

instance [has_zero α] [has_zero β] [has_one β] : has_one (α →₀ β) :=
⟨single 0 1⟩

lemma one_def [has_zero α] [has_zero β] [has_one β] : 1 = (single 0 1 : α →₀ β) :=
rfl

section comap_domain

variables {α' : Type u₁} {γ : Type x} {δ : Type y} [has_zero δ]
  {f : α → α'} {hf : injective f} {p : α → Prop}

section zero
variables [has_zero β] {v v' : α' →₀ β}

def comap_domain (f : α → α') (hf : injective f) (v : α' →₀ β) : α →₀ β :=
⟨λa, v.1 (f a), finite_of_finite_image hf $ finite_subset v.2 $ image_subset_iff.mpr $ subset.refl _⟩

@[simp] lemma comap_domain_apply {a : α} : (comap_domain f hf v) a = v (f a) :=
rfl

@[simp] lemma comap_domain_zero : (0:α' →₀ β).comap_domain f hf  = 0 :=
rfl

lemma sum_comap_domain_index [add_comm_monoid γ]
  {h : α' → β → γ} (hvf : ∀a'∈v.support, ∃a, f a = a' ) :
  (v.comap_domain f hf).sum (λa b, h (f a) b) = v.sum h :=
begin
  refine finset.sum_bij (assume a ha, f a) _ _ _ _; simp,
  exact (assume a₁ a₂ _ _ eq, hf eq),
  exact (assume a' ha',
    have a' ∈ v.support, by simpa,
    let ⟨a, eq⟩ := hvf _ this in ⟨a, eq.symm ▸ ha', eq.symm⟩)
end

def subtype_domain (p : α → Prop) : (α →₀ β) → (subtype p →₀ β) :=
comap_domain subtype.val $ assume a₁ a₂, subtype.eq

lemma sum_subtype_domain_index  [add_comm_monoid γ] {v : α →₀ β}
  {h : α → β → γ} (hp : ∀x∈v.support, p x) :
  (v.subtype_domain p).sum (λa b, h a.1 b) = v.sum h :=
sum_comap_domain_index (assume a ha, ⟨⟨a, hp a ha⟩, rfl⟩)

@[simp] lemma subtype_domain_apply {a : subtype p} {v : α →₀ β} :
  (subtype_domain p v) a = v (a.val) :=
rfl

@[simp] lemma subtype_domain_zero : subtype_domain p (0 : α →₀ β) = 0 := rfl

end zero

section monoid
variables [add_monoid β] {v v' : α' →₀ β}

@[simp] lemma comap_domain_add :
  (v + v').comap_domain f hf = v.comap_domain f hf + v'.comap_domain f hf := rfl

@[simp] lemma subtype_domain_add {v v' : α →₀ β} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p := rfl

end monoid

section comm_monoid
variables [add_comm_monoid β]

lemma comap_domain_sum {s : finset γ} {h : γ → α' →₀ β} :
  (s.sum h).comap_domain f hf = s.sum (λc, (h c).comap_domain f hf) :=
eq.symm (finset.sum_hom _ comap_domain_zero $ assume v v', comap_domain_add)

lemma comap_domain_finsupp_sum {s : γ →₀ δ} {h : γ → δ → α' →₀ β} :
  (s.sum h).comap_domain f hf = s.sum (λc d, (h c d).comap_domain f hf) :=
comap_domain_sum

lemma subtype_domain_sum {s : finset γ} {h : γ → α →₀ β} :
  (s.sum h).subtype_domain p = s.sum (λc, (h c).subtype_domain p) :=
comap_domain_sum

lemma subtype_domain_finsupp_sum {s : γ →₀ δ} {h : γ → δ → α →₀ β} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

end comm_monoid

section group
variables [add_group β] {v v' : α' →₀ β}

@[simp] lemma comap_domain_neg : (- v).comap_domain f hf = - v.comap_domain f hf := rfl

@[simp] lemma comap_domain_sub :
  (v - v').comap_domain f hf = v.comap_domain f hf - v'.comap_domain f hf := rfl

@[simp] lemma subtype_domain_neg {v : α →₀ β} :
  (- v).subtype_domain p = - v.subtype_domain p := rfl

@[simp] lemma subtype_domain_sub {v v' : α →₀ β} :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p := rfl

end group

end comap_domain

section
variables [add_monoid α] [semiring β]

-- TODO: the simplifier unfolds 0 in the instance proof!
private lemma zero_mul (f : α →₀ β) : 0 * f = 0 := by simp [mul_def, sum_zero_index]
private lemma mul_zero (f : α →₀ β) : f * 0 = 0 := by simp [mul_def, sum_zero_index]
private lemma left_distrib (a b c : α →₀ β) : a * (b + c) = a * b + a * c :=
by simp [mul_def, sum_add_index, mul_add]
private lemma right_distrib (a b c : α →₀ β) : (a + b) * c = a * c + b * c :=
by simp [mul_def, sum_add_index, add_mul]

def to_semiring : semiring (α →₀ β) :=
{ one       := 1,
  mul       := (*),
  one_mul   := assume f, by simp [mul_def, one_def, sum_single_index],
  mul_one   := assume f, by simp [mul_def, one_def, sum_single_index],
  zero_mul  := zero_mul,
  mul_zero  := mul_zero,
  mul_assoc := assume f g h,
    by simp [mul_def, sum_sum_index, sum_zero_index, sum_add_index, sum_single_index,
        add_mul, mul_add, mul_assoc],
  left_distrib  := left_distrib,
  right_distrib := right_distrib,
  .. finsupp.add_comm_monoid }

end

local attribute [instance] to_semiring

def to_comm_semiring [add_comm_monoid α] [comm_semiring β] : comm_semiring (α →₀ β) :=
{ mul_comm := assume f g,
  begin
    simp [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp
  end,
  .. finsupp.to_semiring }

local attribute [instance] to_comm_semiring

def to_ring [add_monoid α] [ring β] : ring (α →₀ β) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. finsupp.to_semiring }

def to_comm_ring [add_comm_monoid α] [comm_ring β] : comm_ring (α →₀ β) :=
{ mul_comm := mul_comm, .. finsupp.to_ring}

lemma single_mul_single [has_add α] [semiring β] {a₁ a₂ : α} {b₁ b₂ : β}:
  single a₁ b₁ * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
by simp [mul_def, sum_single_index]

lemma prod_single {ι : Type x} [add_comm_monoid α] [comm_semiring β] {s : finset ι}
  {a : ι → α} {b : ι → β} :
  s.prod (λi, single (a i) (b i)) = single (s.sum a) (s.prod b) :=
 finset.induction_on s (by simp [one_def]) (by simp [single_mul_single] {contextual := tt})

end finsupp
