module

public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Positivity.BigNefCartier
public import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare

/-!
# Big and nef Cartier divisors: the image of a linear system, and top self-intersection

Let `X` be a projective variety of dimension `n` over a field `k` and `D` a Cartier divisor on
`X`. This file proves two of the characterisations of bigness of Kollár–Mori 2.60–2.61.

If for some integer `m > 0` the image `Y_{𝒪(mD)} ⊆ ℙᴺ` of the map `φ_{|mD|}` defined by a
basis of `H⁰(X, 𝒪_X(mD))` has the dimension of `X`, then `D` is big:
`h⁰(X, 𝒪_X(lD)) > c lⁿ` for some `c > 0` and all large `l`. Writing `y = φ_{|mD|}(η_X)`, the
residue field `κ(y)` has transcendence degree `dim Y = n` and is algebraic over the values of the
chart ratios `x_v / x_{v₀}`, so `n` ratios `s_{v_l} / s_{v₀}` of basis sections are
algebraically independent in the function field of `X`; the monomials of degree at most
`⌊j / n⌋` in them give `h⁰(X, 𝒪_X(jmD)) ≥ (⌊j / n⌋ + 1)ⁿ`, and Kodaira's lemma upgrades growth
along the multiples of `m` to bigness.

If `D` is nef (`deg_C 𝒪_X(D) ≥ 0` for every closed curve `C ⊆ X`) and big, then `(Dⁿ) > 0`.
By Kodaira's lemma `mD ∼ A + E` with `m > 0`, `A` ample and `E` effective. Writing
`aⱼ = (Aʲ · Dⁿ⁻ʲ)`, multilinearity gives `m aⱼ = aⱼ₊₁ + (Aʲ · Dⁿ⁻ʲ⁻¹ · E)`, and the last term is
the intersection number of copies of `𝒪_X(A)` and `𝒪_X(D)` against the subscheme `E`, which is
nonnegative by Kleiman's theorem for mixed products of a nef and an ample sheaf. Hence
`mⁿ (Dⁿ) = mⁿ a₀ ≥ aₙ = (Aⁿ) > 0`.

## Main results

* `MMP.Mori.isBigCartier_of_topologicalKrullDim_linearSystemImage_eq`: Kollár–Mori 2.60,
  (4) ⇒ (1).
* `MMP.Mori.sheafSelfIntersectionNumber_pos_of_isNef_of_isBigCartier`: `(Dⁿ) > 0` for a nef and
  big Cartier divisor `D` on a projective variety of dimension `n` (Kollár–Mori 2.61,
  (1) ⇒ (2)).

## Implementation notes

The image `Y_{𝒪(mD)}` is `MMP.Mori.linearSystemImage` for a basis `b` of `H⁰(X, 𝒪_X(mD))`;
the hypothesis is asked of one basis, any index type. Another basis changes `φ_{|mD|}` by an
automorphism of `ℙᴺ`, so the condition does not depend on the choice.

The source bounds `(rm)ⁿ (Dⁿ) ≥ ((rA)ⁿ)` by cutting with a general member of the very ample
system `|rA|`. Here the inequality `m aⱼ ≥ aⱼ₊₁` is proved one slot at a time by cutting with
the effective divisor `E` instead, which needs neither very ampleness nor a Bertini theorem.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.60, 2.61
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

/-- If `h⁰(X, 𝒪_X(mD)) > c mⁿ` for some `c > 0` and infinitely many `m`, then `D` is big. -/
private theorem isBigCartier_of_growth {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hX : IsProjectiveVariety k f)
    (D : X.CartierDivisor) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hD : ∃ c : ℝ, 0 < c ∧
      {m : ℕ | c * (m : ℝ) ^ n < (cartierH0 k f (m • D) : ℝ)}.Infinite) :
    IsBigCartier k f D := by
  have : IsIntegral X := hX.toIsIntegral
  obtain ⟨m, hm, A, E, -, hA, hE, hlin⟩ :=
    exists_linearlyEquivalent_ample_add_effective f hX hn D hD
  refine MMP.Mori.isBigCartier_of_linearlyEquivalent_add hX (m := (m : ℤ)) (A := A)
    (by exact_mod_cast hm) ?_ hE ?_
  · exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Iso.refl (MMP.CartierDivisor.sheaf A))).mp hA
  · simpa [natCast_zsmul] using hlin

/-- A lower bound `h⁰(X, 𝒪_X(jmD)) ≥ (⌊j / n⌋ + 1)ⁿ` along the multiples of `m` gives
`h⁰(X, 𝒪_X(ND)) > c Nⁿ` for some `c > 0` and infinitely many `N`. -/
private theorem growth_of_pow_le {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.CartierDivisor) {m n : ℕ} (hm : 0 < m)
    (h : ∀ j : ℕ, (j / n + 1) ^ n ≤ cartierH0 k f ((j * m) • D)) :
    ∃ c : ℝ, 0 < c ∧
      {N : ℕ | c * (N : ℝ) ^ n < (cartierH0 k f (N • D) : ℝ)}.Infinite := by
  have hB : (0 : ℝ) < (n : ℝ) * m + 1 := by positivity
  refine ⟨1 / (2 * ((n : ℝ) * m + 1) ^ n), by positivity, ?_⟩
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => j * m)
    (fun j j' hj => Nat.eq_of_mul_eq_mul_right hm hj) fun j => ?_
  simp only [Set.mem_setOf_eq]
  have hx : ((j * m : ℕ) / ((n : ℝ) * m + 1)) ^ n ≤ (((j / n + 1 : ℕ)) : ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · refine pow_le_pow_left₀ (by positivity) ?_ n
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : ((j * m : ℕ) : ℝ) / ((n : ℝ) * m + 1) ≤ (j : ℝ) / n := by
        rw [div_le_div_iff₀ hB hn']
        push_cast
        nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have h2 : (j : ℝ) / n < ((j / n : ℕ) : ℝ) + 1 := by
        have := Nat.lt_floor_add_one ((j : ℝ) / n)
        rwa [Nat.floor_div_eq_div] at this
      push_cast at h1 h2 ⊢
      linarith
  have hy : (1 : ℝ) ≤ (((j / n + 1 : ℕ)) : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_pos _)
  have hc : 1 / (2 * ((n : ℝ) * m + 1) ^ n) * ((j * m : ℕ) : ℝ) ^ n =
      (1 / 2) * ((j * m : ℕ) / ((n : ℝ) * m + 1)) ^ n := by
    rw [div_pow]
    field_simp
  have hh : (((j / n + 1 : ℕ)) : ℝ) ^ n ≤ (cartierH0 k f ((j * m) • D) : ℝ) := by
    exact_mod_cast h j
  rw [hc]
  linarith

/-! ### Counting monomials in algebraically independent ratios -/

section Counting

open MMP.CartierDivisor
open MMP.CartierDivisorSheaf
open Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The section `1` of `𝒦_X` is a global section of `𝒪_X(0)`. -/
private theorem mem_zero_one : Mem (0 : X.CartierDivisor) ⊤ 1 :=
  MMP.CartierDivisor.mem_one_top_of_isEffective MMP.CartierDivisor.isEffective_zero

private theorem mem_pow {F : X.CartierDivisor} {s : X.totalQuotientSheaf.obj.obj (op ⊤)}
    (hs : Mem F ⊤ s) (N : ℕ) : Mem (N • F) ⊤ (s ^ N) := by
  induction N with
  | zero => simpa using mem_zero_one
  | succ N ih =>
    rw [pow_succ, succ_nsmul]
    exact MMP.CartierDivisorSheaf.mem_mul ih hs

private theorem mem_prod {F : X.CartierDivisor} {ι : Type*} (S : Finset ι) (c : ι → ℕ)
    (g : ι → X.totalQuotientSheaf.obj.obj (op ⊤)) (hg : ∀ i ∈ S, Mem (c i • F) ⊤ (g i)) :
    Mem ((∑ i ∈ S, c i) • F) ⊤ (∏ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using mem_zero_one
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_smul]
    exact MMP.CartierDivisorSheaf.mem_mul (hg a (Finset.mem_insert_self a S))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private theorem scalarsToGlobalSections_eq (f : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k f =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom := by
  have : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

/-- On a proper `k`-scheme the global sections of `𝒪_X(F)` are finite-dimensional over `k`. -/
private theorem finiteDimensional_sections (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.CartierDivisor) :
    letI := Module.compHom Γ(sheaf F, ⊤) (scalarsToGlobalSections k f)
    FiniteDimensional k Γ(sheaf F, ⊤) := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
    (sheaf F) 1
  have := finiteDimensional_cohomologyOverField_of_isProper k f (sheaf F) 0
  have e := (cohomologyOverFieldZeroLinearIso k f (sheaf F)).toLinearEquiv
  have key : ∀ φ : k →+* Γ(X, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(sheaf F, ⊤) φ; FiniteDimensional k Γ(sheaf F, ⊤)) := by
    rintro φ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq f)

variable [IsIntegral X]

/-- On an integral scheme, `R(X) ≃ Γ(X, 𝒦_X)`. -/
private noncomputable def ofFunctionFieldEquiv :
    X.functionField ≃+* X.totalQuotientSheaf.obj.obj (op ⊤) :=
  RingEquiv.ofBijective _ (ofFunctionField_bijective ⊤ ⟨genericPoint X, trivial⟩)

/-- The rational function of a global section of `𝒪_X(F)`. -/
private noncomputable def ratFun {F : X.CartierDivisor} (s : Γ(sheaf F, ⊤)) : X.functionField :=
  ofFunctionFieldEquiv.symm (MMP.CartierDivisorSheaf.sectionVal s)

private theorem ofFunctionFieldEquiv_ratFun {F : X.CartierDivisor}
    (s : Γ(sheaf F, ⊤)) : ofFunctionFieldEquiv (ratFun s) =
        MMP.CartierDivisorSheaf.sectionVal s :=
  ofFunctionFieldEquiv.apply_symm_apply _

private theorem ratFun_injective {F : X.CartierDivisor} :
    Function.Injective (ratFun (X := X) (F := F)) := fun s t h =>
  MMP.CartierDivisorSheaf.sectionVal_injective (ofFunctionFieldEquiv.symm.injective h)

/-- The `k`-structure of the function field: scalars through `f`, then the germ at the generic
point. -/
private noncomputable def kToK (f : X ⟶ Spec (.of k)) : k →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (scalarsToGlobalSections k f)

private theorem ofFunctionFieldEquiv_germ (a : Γ(X, ⊤)) :
    ofFunctionFieldEquiv (X.presheaf.germ ⊤ (genericPoint X) trivial a) = toK ⊤ a :=
  functionFieldToTotalQuotientSheaf_germ X ⊤ a trivial

private theorem ratFun_add {F : X.CartierDivisor} (s t : Γ(sheaf F, ⊤)) :
    ratFun (s + t) = ratFun s + ratFun t :=
  map_add ofFunctionFieldEquiv.symm (MMP.CartierDivisorSheaf.sectionVal s)
      (MMP.CartierDivisorSheaf.sectionVal t)

private theorem ratFun_smul (f : X ⟶ Spec (.of k)) {F : X.CartierDivisor} (c : k)
    (s : Γ(sheaf F, ⊤)) :
    letI := Module.compHom Γ(sheaf F, ⊤) (scalarsToGlobalSections k f)
    ratFun (c • s) = kToK f c * ratFun s := by
  letI := Module.compHom Γ(sheaf F, ⊤) (scalarsToGlobalSections k f)
  apply ofFunctionFieldEquiv.injective
  rw [ofFunctionFieldEquiv_ratFun, map_mul, ofFunctionFieldEquiv_ratFun,
    kToK, RingHom.comp_apply]
  erw [ofFunctionFieldEquiv_germ]
  rfl

/-- **Monomials in algebraically independent ratios.** If `σ₀, σ₁, …, σₙ` are global sections of
`𝒪_X(F)` with `σ₀ ≠ 0` and the ratios `σ_l / σ₀` algebraically independent over `k`, then the
monomials `σ₀^{j - |a|} ∏ σ_l^{a_l}` with all `a_l ≤ j / n` are linearly independent sections of
`𝒪_X(jF)`, so `h⁰(X, 𝒪_X(jF)) ≥ (⌊j / n⌋ + 1)ⁿ`. -/
private theorem pow_le_cartierH0 (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.CartierDivisor)
    {n : ℕ} (σ₀ : Γ(sheaf F, ⊤)) (σ : Fin n → Γ(sheaf F, ⊤)) (h₀ : ratFun σ₀ ≠ 0)
    (hind : letI := (kToK f).toAlgebra
      AlgebraicIndependent k (fun l => ratFun (σ l) / ratFun σ₀)) (j : ℕ) :
    (j / n + 1) ^ n ≤ cartierH0 k f (j • F) := by
  classical
  letI := (kToK f).toAlgebra
  letI := Module.compHom Γ(sheaf (j • F), ⊤) (scalarsToGlobalSections k f)
  haveI := finiteDimensional_sections f (j • F)
  set t : Fin n → X.functionField := fun l => ratFun (σ l) / ratFun σ₀ with ht
  -- exponent vectors
  let ex : (Fin n → Fin (j / n + 1)) → (Fin n →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (fun l => (a l : ℕ))
  have hex : Function.Injective ex := by
    intro a a' h
    funext l
    exact Fin.ext (by simpa [ex] using congrArg (fun e : Fin n →₀ ℕ => e l) h)
  have htot : ∀ a : Fin n → Fin (j / n + 1), ∑ l, (a l : ℕ) ≤ j := by
    intro a
    calc ∑ l, (a l : ℕ) ≤ ∑ _l : Fin n, j / n :=
          Finset.sum_le_sum fun l _ => Nat.lt_succ_iff.mp (a l).2
      _ = n * (j / n) := by simp
      _ ≤ j := Nat.mul_div_le j n
  -- the monomial sections
  have hmem : ∀ a : Fin n → Fin (j / n + 1), Mem (j • F) ⊤
      (MMP.CartierDivisorSheaf.sectionVal σ₀ ^ (j - ∑ l, (a l : ℕ)) * ∏ l,
          MMP.CartierDivisorSheaf.sectionVal (σ l) ^ (a l : ℕ)) := by
    intro a
    have h1 := mem_pow (show Mem F ⊤ (MMP.CartierDivisorSheaf.sectionVal σ₀) from
      (show ↥((sheafSubmodule F).obj (op ⊤)) from σ₀).2) (j - ∑ l, (a l : ℕ))
    have h2 := mem_prod (F := F) Finset.univ (fun l => (a l : ℕ))
      (fun l => MMP.CartierDivisorSheaf.sectionVal (σ l) ^ (a l : ℕ)) (fun l _ => mem_pow
        (show Mem F ⊤ (MMP.CartierDivisorSheaf.sectionVal (σ l)) from
          (show ↥((sheafSubmodule F).obj (op ⊤)) from σ l).2) _)
    have h3 := MMP.CartierDivisorSheaf.mem_mul h1 h2
    rwa [← add_smul, Nat.sub_add_cancel (htot a)] at h3
  let M : (Fin n → Fin (j / n + 1)) → Γ(sheaf (j • F), ⊤) := fun a =>
    (⟨_, hmem a⟩ : ↥((sheafSubmodule (j • F)).obj (op ⊤)))
  have hM : ∀ a, ratFun (M a) =
      ratFun σ₀ ^ (j - ∑ l, (a l : ℕ)) * ∏ l, ratFun (σ l) ^ (a l : ℕ) := by
    intro a
    apply ofFunctionFieldEquiv.injective
    rw [ofFunctionFieldEquiv_ratFun, map_mul, map_pow, map_prod]
    simp only [map_pow, ofFunctionFieldEquiv_ratFun]
    rfl
  -- the `k`-linear map `s ↦ s / σ₀ʲ`
  let Θ : Γ(sheaf (j • F), ⊤) →ₗ[k] X.functionField :=
    { toFun := fun s => ratFun s / ratFun σ₀ ^ j
      map_add' := fun s s' => by rw [ratFun_add, add_div]
      map_smul' := fun c s => by
        rw [ratFun_smul f c s, RingHom.id_apply, Algebra.smul_def, mul_div_assoc]
        rfl }
  have hΘ : ∀ a, Θ (M a) = MvPolynomial.aeval t (MvPolynomial.monomial (ex a) (1 : k)) := by
    intro a
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    change ratFun (M a) / ratFun σ₀ ^ j = _
    simp only [hM, ex, Finsupp.coe_equivFunOnFinite_symm, ht, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    have hj : ratFun σ₀ ^ j =
        ratFun σ₀ ^ (j - ∑ l, (a l : ℕ)) * ratFun σ₀ ^ (∑ l, (a l : ℕ)) := by
      rw [← pow_add, Nat.sub_add_cancel (htot a)]
    rw [hj, mul_div_mul_left _ _ (pow_ne_zero _ h₀)]
  have hli : LinearIndependent k (fun a => MvPolynomial.aeval t (MvPolynomial.monomial (ex a)
      (1 : k))) :=
    ((MvPolynomial.basisMonomials (Fin n) k).linearIndependent.comp ex hex).map'
      (MvPolynomial.aeval t).toLinearMap (LinearMap.ker_eq_bot.mpr hind)
  have hliM : LinearIndependent k M :=
    LinearIndependent.of_comp Θ (by simpa only [Function.comp_def, hΘ] using hli)
  simpa [cartierH0] using hliM.fintype_card_le_finrank

/-- On a nonempty open `W`, the comparison `R(X) → 𝒦_X(W)` restricts the global comparison. -/
private theorem app_functionField_eq_resK (W : X.Opens) (r : X.functionField) :
    (functionFieldToTotalQuotientSheaf X).app (op W) r =
      resK le_top (ofFunctionFieldEquiv r) := by
  have h := ConcreteCategory.congr_hom
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE (le_top : W ≤ ⊤)).op) r
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

/-- **A ratio of sections, read in the function field.** If `s|_W = ρ · t|_W` for sections
`s, t` of `𝒪_X(F)` and a function `ρ` on an open `W` containing the generic point, then the
rational function of `s` is the germ of `ρ` times that of `t`. -/
private theorem ratFun_eq_germ_mul {F : X.CartierDivisor} {W : X.Opens}
    (hW : genericPoint X ∈ W) (s t : Γ(sheaf F, ⊤)) (ρ : Γ(X, W))
    (h : (sheaf F).presheaf.map (homOfLE le_top : W ⟶ ⊤).op s =
      ρ • (sheaf F).presheaf.map (homOfLE le_top : W ⟶ ⊤).op t) :
    ratFun s = X.presheaf.germ W (genericPoint X) hW ρ * ratFun t := by
  apply functionFieldToTotalQuotientSheaf_app_injective X W ⟨_, hW⟩
  rw [map_mul, functionFieldToTotalQuotientSheaf_germ, app_functionField_eq_resK,
    app_functionField_eq_resK, ofFunctionFieldEquiv_ratFun,
    ofFunctionFieldEquiv_ratFun]
  exact congrArg MMP.CartierDivisorSheaf.sectionVal h

end Counting

/-! ### The standard chart of `𝐏(k^{(ι)})` -/

section Chart

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (grading degreeOneElement)
open HomogeneousLocalization

variable (k : Type u) [Field k] {ι : Type u}

/-- The coordinate `x_v` of `𝐏(k^{(ι)})`, an element of degree one of `Sym_k(k^{(ι)})`. -/
private noncomputable abbrev coord (v : ι) : SymmetricAlgebra k (ι →₀ k) :=
  (degreeOneElement k (ι →₀ k) (Finsupp.single v 1) : SymmetricAlgebra k (ι →₀ k))

private theorem coord_mem (v : ι) : coord k v ∈ grading k (ι →₀ k) 1 :=
  (degreeOneElement k (ι →₀ k) (Finsupp.single v 1)).2

/-- The degree-zero fraction `x_v / x_{v₀}`. -/
private noncomputable def coordRatio (v₀ v : ι) : Away (grading k (ι →₀ k)) (coord k v₀) :=
  Away.mk (grading k (ι →₀ k)) (coord_mem k v₀) 1 (coord k v) (by simpa using coord_mem k v)

/-- The degree-zero part of `Sym_k V` is `k`. -/
private theorem exists_algebraMap_eq (z : grading k (ι →₀ k) 0) :
    ∃ r : k, algebraMap k (grading k (ι →₀ k) 0) r = z := by
  have hz := z.2
  simp only [Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.grading,
    SymPow.symmetricPower, pow_zero, Submodule.one_eq_range] at hz
  obtain ⟨r, hr⟩ := hz
  exact ⟨r, Subtype.ext hr⟩

/-- `Sym_k V` is generated over its degree-zero part by the coordinates. -/
private theorem adjoin_range_coord :
    Algebra.adjoin (grading k (ι →₀ k) 0) (Set.range (coord k (ι := ι))) = ⊤ := by
  have hsc : ∀ (r : k) (x : SymmetricAlgebra k (ι →₀ k)),
      r • x = (algebraMap k (grading k (ι →₀ k) 0) r) • x := by
    intro r x
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  rw [eq_top_iff]
  rintro a -
  induction a using SymmetricAlgebra.induction with
  | ι w =>
    rw [← Finsupp.sum_single w, map_finsuppSum]
    refine Subalgebra.sum_mem _ fun v _ => ?_
    change SymmetricAlgebra.ι k _ (Finsupp.single v (w v)) ∈ _
    have h1 : Finsupp.single v (w v) = w v • Finsupp.single v (1 : k) := by simp
    rw [h1, map_smul, hsc]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self v)) _
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem
      (Algebra.adjoin (grading k (ι →₀ k) 0) (Set.range (coord k (ι := ι))))
      (algebraMap k (grading k (ι →₀ k) 0) r)
  | add x y hx hy => exact add_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy

/-- A monomial `∏ x_v ^ {a_v} / x_{v₀} ^ {∑ a_v}` is the product of the powers of the ratios. -/
private theorem away_mk_prod_eq [Fintype ι] (v₀ : ι) (a : ℕ) (ai : ι → ℕ) (hai : ∑ x, ai x = a)
    (h : ∏ i, coord k i ^ ai i ∈ grading k (ι →₀ k) (a • 1)) :
    Away.mk (grading k (ι →₀ k)) (coord_mem k v₀) a (∏ i, coord k i ^ ai i) h =
      ∏ i, coordRatio k v₀ i ^ ai i := by
  apply HomogeneousLocalization.val_injective
  symm
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, Away.val_mk, coordRatio,
    Localization.mk_pow, Localization.mk_prod]
  congr 1
  ext
  simp [← hai, Finset.prod_pow_eq_pow_sum]

/-- The chart ring `Sym_k(k^{(ι)})_{(x_{v₀})}` is generated over the degree-zero part by the
ratios `x_v / x_{v₀}`. -/
private theorem adjoin_range_coordRatio [Fintype ι] (v₀ : ι) :
    Algebra.adjoin (grading k (ι →₀ k) 0) (Set.range (coordRatio k v₀)) = ⊤ := by
  classical
  rw [eq_top_iff, ← Away.adjoin_mk_prod_pow_eq_top (coord_mem k v₀) ι (coord k)
    (adjoin_range_coord k) (fun _ => 1) (fun i => by simpa using coord_mem k i)]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨a, ai, hai, -, rfl⟩
  rw [SetLike.mem_coe, away_mk_prod_eq k v₀ a ai (by simpa using hai)]
  exact Subalgebra.prod_mem _ fun i _ =>
    Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _

end Chart

/-! ### Transcendence bases inside a generating family -/

section Transcendence

/-- If a field `κ` is algebraic over the subalgebra generated by a family `t` and has
transcendence degree `n`, then `n` members of the family are algebraically independent. -/
private theorem exists_algebraicIndependent_comp {k κ ι : Type u} [Field k] [Field κ]
    [Algebra k κ] (t : ι → κ) [Algebra.IsAlgebraic (Algebra.adjoin k (Set.range t)) κ] {n : ℕ}
    (h : Cardinal.toENat (Algebra.trdeg k κ) = n) :
    ∃ v : Fin n → ι, AlgebraicIndependent k (t ∘ v) := by
  classical
  obtain ⟨T, hT, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (Set.range t)
  have hcard : Cardinal.mk T = n := by
    rw [hb.cardinalMk_eq_trdeg]
    exact Cardinal.toENatAux_eq_nat.mp h
  have hfin : Finite T :=
    Cardinal.lt_aleph0_iff_finite.mp (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have : Fintype T := Fintype.ofFinite T
  have e : Fin n ≃ T := (Fintype.equivFinOfCardEq (by
    rw [Cardinal.mk_fintype] at hcard; exact_mod_cast hcard)).symm
  choose g hg using fun x : T => hT x.2
  refine ⟨g ∘ e, ?_⟩
  have : t ∘ (g ∘ e) = Subtype.val ∘ e := funext fun l => hg (e l)
  rw [this]
  exact hb.1.comp e e.injective

/-- A field is algebraic over a subalgebra of which it is the field of fractions. -/
private theorem isAlgebraic_of_forall_eq_div {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (R : Subalgebra k κ) (h : ∀ z : κ, ∃ a ∈ R, ∃ b ∈ R, z = a / b) :
    Algebra.IsAlgebraic R κ := by
  constructor
  intro z
  obtain ⟨a, ha, b, hb, rfl⟩ := h z
  rw [div_eq_mul_inv]
  exact (isAlgebraic_algebraMap (⟨a, ha⟩ : R)).mul (isAlgebraic_algebraMap (⟨b, hb⟩ : R)).inv

end Transcendence

/-! ### Sections, restriction and the chart ring maps -/

section Sections

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.NonvanishingOpen (nonvanishingOpen)

/-- Every element of the residue field at a point of an affine open `W` is a quotient of two
evaluations of sections over `W`. -/
private theorem exists_eq_evaluation_div {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
    (x : Z) (hx : x ∈ W) (z : Z.residueField x) :
    ∃ a s : Γ(Z, W), Z.evaluation W x hx s ≠ 0 ∧
      z = Z.evaluation W x hx a / Z.evaluation W x hx s := by
  obtain ⟨g, rfl⟩ := Z.residue_surjective x z
  letI := TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨x, hx⟩ : W)
  have hloc := hW.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl g
  have hu : IsUnit (algebraMap Γ(Z, W) (Z.presheaf.stalk x) s) :=
    IsLocalization.map_units _ s
  have hs : Z.evaluation W x hx s ≠ 0 := by
    rw [← Scheme.germ_residue]
    exact (hu.map (Z.residue x).hom).ne_zero
  refine ⟨a, s, hs, ?_⟩
  rw [eq_div_iff hs, ← Scheme.germ_residue]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  exact IsLocalization.mk'_spec _ a s

/-- Pulling a global section back along the inclusion of an open is restricting it, read
through `Scheme.Modules.restrictFunctorIsoPullback`. -/
private theorem pullbackGlobalSections_ι_eq {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (s : Γ(M, ⊤)) :
    pullbackGlobalSections U.ι M s =
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M).app ⊤
        (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op s) := by
  have h := (Scheme.Modules.restrictAdjunction U.ι).unit_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M
  rw [pullbackGlobalSections, ← h]
  set Φ := ((Scheme.Modules.restrictAdjunction U.ι).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).hom.app M
  change _ = Φ.app ⊤ _
  have hn := Φ.mapPresheaf.naturality (eqToHom (U.ι.preimage_top).symm).op
  simp only [Scheme.Modules.mapPresheaf_app] at hn
  have hn' := ConcreteCategory.congr_hom hn
    (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app ⊤ s)
  simp only [ConcreteCategory.comp_apply] at hn'
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [← hn']
  refine (ConcreteCategory.comp_apply _ _ _).trans
    (congrArg (ConcreteCategory.hom (Φ.app ⊤)) ?_)
  have e : M.presheaf.map (homOfLE (U.ι.image_preimage_le ⊤)).op ≫
      M.presheaf.map (U.ι.opensFunctor.map (eqToHom (U.ι.preimage_top).symm)).op =
      M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom e s

/-- A relation `s|_W = ρ · t|_W` between pulled-back global sections over an open `W` of `U ⊆ X`
is the relation `s|_{W} = ρ · t|_{W}` on `X`, with `W` and `ρ` read in `X`. -/
private theorem restrict_eq_smul_of_pullback {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (W : U.toScheme.Opens) (s t : Γ(M, ⊤)) (ρ : Γ(U.toScheme, W))
    (h : ((Scheme.Modules.pullback U.ι).obj M).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (pullbackGlobalSections U.ι M s) =
      ρ • ((Scheme.Modules.pullback U.ι).obj M).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (pullbackGlobalSections U.ι M t)) :
    M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op s =
      (U.ι.appIso W).inv ρ • M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op t := by
  set Φ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  rw [pullbackGlobalSections_ι_eq, pullbackGlobalSections_ι_eq] at h
  have hs := Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app Φ.hom (le_top : W ≤ ⊤)
    (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op s)
  have ht := Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app Φ.hom (le_top : W ≤ ⊤)
    (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op t)
  erw [hs, ht, ← Scheme.Modules.Hom.app_smul] at h
  have hinv : ∀ x, Φ.inv.app W (Φ.hom.app W x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  have h3 := congrArg (Φ.inv.app W) h
  rw [hinv, hinv] at h3
  have e : ∀ x : Γ(M, ⊤), (M.restrict U.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
      (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op x) =
      M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op x := fun x => by
    have e0 : M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        M.presheaf.map (U.ι.opensFunctor.map (homOfLE (le_top : W ≤ ⊤))).op =
        M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op := by
      rw [← Functor.map_comp]
      congr 1
    exact ConcreteCategory.congr_hom e0 x
  erw [e, e] at h3
  exact h3

attribute [local instance] globalSectionsModule in
/-- **The chart ring map of `φ_{ℒ,ψ}` on a degree-one fraction.** Over the nonvanishing open `W`
of `ψ(v₀)`, the restriction of `ψ(v)` is the function induced by `φ_{ℒ,ψ}` from `v / v₀` times
the restriction of `ψ(v₀)`. -/
private theorem resTop_eq_appLE_smul (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L]
    (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen Y L (ψ v) = ⊤) (v₀ v : V)
    (W : Y.Opens)
    (hW : W = Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nvOpen (grading k V)
        (veroneseOfLinearMap k V L ψ) (degreeOneElement k V v₀))
    (hle : W ≤ morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v₀))
    (hv : SymmetricAlgebra.ι k V v ∈ grading k V (1 • 1)) :
    L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ψ v) =
      (morphismOfGeneratingSections k V L ψ hψ).appLE _ W hle
        ((Proj.awayToSection (grading k V) (SymmetricAlgebra.ι k V v₀)).hom
          (HomogeneousLocalization.Away.mk (grading k V) (degreeOneElement k V v₀).2 1
            (SymmetricAlgebra.ι k V v) hv)) •
      L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ψ v₀) := by
  subst hW
  have hc := (classifies_classifyingPair k V L ψ hψ).2.2 (degreeOneElement k V v₀) hle
  erw [hc]
  set ψ' := veroneseOfLinearMap k V L ψ
  have hv1 : SymmetricAlgebra.ι k V v ∈ grading k V (1 * 1) := by simpa using hv
  have key := ψ'.resTop_eq_lift_smul (degreeOneElement k V v₀).2 le_rfl Nat.one_pos 1
    (SymmetricAlgebra.ι k V v) hv ⟨_, hv1⟩ rfl
  have ht := ψ'.toFun_eq_pow (degreeOneElement k V v).2 1 ⟨_, hv1⟩ (pow_one _).symm
  rw [ht] at key
  set e := Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L
  have hu := congrArg (e.hom.app _) key
  rw [Scheme.Modules.Hom.app_smul] at hu
  have h1 : ∀ (W : Y.Opens) x,
      e.hom.app W (Stacks.TensorPowerTrivialize.resTop _ x W) =
        L.presheaf.map (homOfLE le_top).op (e.hom.app ⊤ x) :=
    fun W x => (Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app _ le_top x).symm
  have h2 : ∀ w : V, e.hom.app ⊤ (ψ'.pow (degreeOneElement k V w).2 1) = ψ w := fun w => by
    rw [pow_degreeOneElement, unitorPow_app_twistOneSection]
  rw [h1, h1, h2, h2] at hu
  exact hu

end Sections

/-! ### The image of the linear system -/

section Image

open MMP.CartierDivisor
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec)

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Evaluating a restricted section at a point is evaluating the section. -/
private theorem evaluation_map {Z : Scheme.{u}} {V V' : Z.Opens} (i : V' ⟶ V) (x : Z)
    (hx : x ∈ V') (a : Γ(Z, V)) :
    Z.evaluation V' x hx (Z.presheaf.map i.op a) = Z.evaluation V x (leOfHom i hx) a := by
  rw [← Scheme.germ_residue, ← Scheme.germ_residue, CommRingCat.comp_apply,
    CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- **The chart ratios carry the transcendence degree.** At a point `y` of the chart
`D₊(x_{v₀})` of `𝐏(k^{(ι)})`, the residue field `κ(y)` is algebraic over the `k`-algebra
generated by the values at `y` of the ratios `x_v / x_{v₀}`; so if `κ(y)` has transcendence
degree `n`, then `n` of these values are algebraically independent over `k`. -/
private theorem exists_algebraicIndependent_coordRatio {ι : Type u} [Fintype ι] (v₀ : ι)
    {y : projectiveSpaceOfModule k (ι →₀ k)}
    (hy : y ∈ Proj.basicOpen (grading k (ι →₀ k)) (coord k v₀)) {n : ℕ}
    (htr : letI : Algebra k ((projectiveSpaceOfModule k (ι →₀ k)).residueField y) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k (ι →₀ k)).appTop ≫
          (projectiveSpaceOfModule k (ι →₀ k)).Γevaluation y).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k ((projectiveSpaceOfModule k (ι →₀ k)).residueField y)) =
        n) :
    letI : Algebra k ((projectiveSpaceOfModule k (ι →₀ k)).residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k (ι →₀ k)).appTop ≫
        (projectiveSpaceOfModule k (ι →₀ k)).Γevaluation y).hom.toAlgebra
    ∃ v : Fin n → ι, AlgebraicIndependent k fun l =>
      (projectiveSpaceOfModule k (ι →₀ k)).evaluation _ y hy
        ((Proj.awayToSection (grading k (ι →₀ k)) (coord k v₀)).hom (coordRatio k v₀ (v l))) := by
  letI : Algebra k ((projectiveSpaceOfModule k (ι →₀ k)).residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k (ι →₀ k)).appTop ≫
      (projectiveSpaceOfModule k (ι →₀ k)).Γevaluation y).hom.toAlgebra
  set V := ι →₀ k
  set D := Proj.basicOpen (grading k V) (coord k v₀)
  have hdeg := coord_mem k v₀
  let ev : HomogeneousLocalization.Away (grading k V) (coord k v₀) →+*
      (projectiveSpaceOfModule k V).residueField y :=
    ((projectiveSpaceOfModule k V).evaluation D y hy).hom.comp
      (Proj.awayToSection (grading k V) (coord k v₀)).hom
  let t : ι → (projectiveSpaceOfModule k V).residueField y := fun w => ev (coordRatio k v₀ w)
  have hconst : ∀ r : k, ev (HomogeneousLocalization.fromZeroRingHom (grading k V) _
      (algebraMap k (grading k V 0) r)) = algebraMap k _ r := by
    intro r
    have hp : projectiveSpaceOfModuleToSpec k V = Proj.toSpecZero (grading k V) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (grading k V 0))) := rfl
    change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k V).appTop ≫
      (projectiveSpaceOfModule k V).Γevaluation y).hom r
    have hn := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (grading k V 0)))) r
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hp, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← hn]
    generalize algebraMap k (grading k V 0) r = c
    have hc := Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.toSpecZero_appLE_apply
      (grading k V) hdeg one_pos c
    change (projectiveSpaceOfModule k V).evaluation D y hy
      ((Proj.awayToSection (grading k V) (coord k v₀)).hom
        (HomogeneousLocalization.fromZeroRingHom (grading k V) _ c)) = _
    rw [← hc]
    exact evaluation_map _ y hy _
  have hrange : ∀ a, ev a ∈ Algebra.adjoin k (Set.range t) := by
    intro a
    have ha : a ∈ Algebra.adjoin (grading k V 0) (Set.range (coordRatio k v₀)) := by
      rw [adjoin_range_coordRatio]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨w, rfl⟩
    | algebraMap c =>
      obtain ⟨r, rfl⟩ := exists_algebraMap_eq k c
      erw [hconst r]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range t)) _ := by
    apply isAlgebraic_of_forall_eq_div
    intro z
    obtain ⟨a, s, -, rfl⟩ := exists_eq_evaluation_div
      (Proj.isAffineOpen_basicOpen (grading k V) (coord k v₀) hdeg one_pos) y hy z
    have hsurj : ∀ g : Γ(projectiveSpaceOfModule k V, D), ∃ u, ev u =
        (projectiveSpaceOfModule k V).evaluation D y hy g := fun g =>
      ⟨(Proj.basicOpenIsoAway (grading k V) (coord k v₀) hdeg one_pos).inv g, by
        change (projectiveSpaceOfModule k V).evaluation D y hy
          ((Proj.basicOpenIsoAway (grading k V) (coord k v₀) hdeg one_pos).hom
            ((Proj.basicOpenIsoAway (grading k V) (coord k v₀) hdeg one_pos).inv g)) = _
        rw [Iso.inv_hom_id_apply]⟩
    obtain ⟨a', ha'⟩ := hsurj a
    obtain ⟨s', hs'⟩ := hsurj s
    exact ⟨_, ha' ▸ hrange a', _, hs' ▸ hrange s', rfl⟩
  exact exists_algebraicIndependent_comp t htr

/-- The image `Y` of `φ_{|ℒ|}` is homeomorphic to the closure of the range of `φ_{|ℒ|}`, so the
two have the same dimension. -/
private theorem topologicalKrullDim_linearSystemImage (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
    (b : letI := globalSectionsModule k X L; Module.Basis ι k Γ(L, ⊤)) :
    letI := globalSectionsModule k X L
    topologicalKrullDim (linearSystemImage k L b) =
      topologicalKrullDim (closure (Set.range (linearSystemMap k L b).base)) := by
  letI := globalSectionsModule k X L
  rw [linearSystemImage, (linearSystemImageIdeal k L b).subschemeι.isClosedEmbedding.isEmbedding
    |>.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  have : Set.range (linearSystemImageIdeal k L b).subschemeι.base =
      closure (Set.range (linearSystemMap k L b).base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, linearSystemImageIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [this]

/-- **`n` ratios of a basis of `H⁰(X, 𝒪_X(F))` are algebraically independent.** If the image
`Y` of `φ_{|F|}` has dimension `n`, then for some `v₀` with `s_{v₀} ≠ 0` and some `v₁, …, vₙ`,
the rational functions `s_{v_l} / s_{v₀}` are algebraically independent over `k`. -/
private theorem exists_algebraicIndependent_ratio (f : X ⟶ Spec (.of k))
    (hX : IsProjectiveVariety k f) [IsIntegral X] (F : X.CartierDivisor) {ι : Type u}
    (b : letI : X.Over (Spec (.of k)) := ⟨f⟩
      letI := globalSectionsModule k X (sheaf F)
      Module.Basis ι k Γ(sheaf F, ⊤)) {n : ℕ}
    (hY : letI : X.Over (Spec (.of k)) := ⟨f⟩
      letI := globalSectionsModule k X (sheaf F)
      topologicalKrullDim (linearSystemImage k (sheaf F) b) = n) :
    ∃ (v₀ : ι) (v : Fin n → ι), ratFun (b v₀) ≠ 0 ∧
      letI := (kToK f).toAlgebra
      AlgebraicIndependent k (fun l => ratFun (b (v l)) / ratFun (b v₀)) := by
  classical
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  letI := globalSectionsModule k X (sheaf F)
  have : IsProper f := isProper_of_isProjectiveMorphism f hX.isProjective
  haveI : FiniteDimensional k Γ(sheaf F, ⊤) := finiteDimensional_sections f F
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hdim : topologicalKrullDim
      (closure (Set.range (linearSystemMap k (sheaf F) b).base)) = n :=
    (topologicalKrullDim_linearSystemImage k (sheaf F) b).symm.trans hY
  -- the generic point of `X` lies in `U`
  have hηU : genericPoint X ∈ linearSystemLocus k (sheaf F) b := by
    have hne : Nonempty (TopologicalSpace.IrreducibleCloseds
        (closure (Set.range (linearSystemMap k (sheaf F) b).base))) := by
      rw [← Order.krullDim_ne_bot_iff]
      change topologicalKrullDim _ ≠ ⊥
      rw [hdim]
      exact WithBot.coe_ne_bot
    obtain ⟨Z⟩ := hne
    obtain ⟨p, -⟩ := Z.isIrreducible.nonempty
    obtain ⟨-, ⟨x, -⟩⟩ := closure_nonempty_iff.mp ⟨p.1, p.2⟩
    exact ((genericPoint_spec X).mem_open_set_iff (linearSystemLocus k (sheaf F) b).isOpen).mpr
      ⟨x.1, trivial, x.2⟩
  -- notation
  set V := ι →₀ k
  set U := linearSystemLocus k (sheaf F) b
  set ψ := linearSystemRestrict k (sheaf F) b
  have hψ := iSup_nonvanishingOpen_linearSystemRestrict k (sheaf F) b
  have hψv : ∀ w, ψ (Finsupp.single w 1) = pullbackGlobalSections U.ι (sheaf F) (b w) :=
    fun w => by
      simp only [ψ, linearSystemRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Module.Basis.repr_symm_single_one]
      rfl
  obtain ⟨v₀, hv₀⟩ := (mem_linearSystemLocus_iff k (sheaf F) b _).1 hηU
  let ηU : U.toScheme := ⟨genericPoint X, hηU⟩
  set φ := linearSystemMap k (sheaf F) b
  set W := Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nvOpen (grading k V)
    (veroneseOfLinearMap k V _ ψ) (degreeOneElement k V (Finsupp.single v₀ 1)) with hWdef
  have hcl := classifies_classifyingPair k V _ ψ hψ
  have hle : W ≤ φ ⁻¹ᵁ Proj.basicOpen (grading k V) (coord k v₀) :=
    ((hcl.1 (degreeOneElement k V (Finsupp.single v₀ 1))).symm).le
  have hηW : ηU ∈ W := by
    rw [hWdef, Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nvOpen, pow_degreeOneElement,
      nonvanishingOpen_twistOneSection, hψv,
      Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
    exact hv₀
  set D := Proj.basicOpen (grading k V) (coord k v₀)
  set y := φ.base ηU
  have hy : y ∈ D := hle hηW
  haveI : Nonempty ι := ⟨v₀⟩
  letI algκ : Algebra k ((projectiveSpaceOfModule k V).residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k V).appTop ≫
      (projectiveSpaceOfModule k V).Γevaluation y).hom.toAlgebra
  -- the transcendence degree of `κ(y)` is `dim Y`
  have htr :
      Cardinal.toENat (Algebra.trdeg k ((projectiveSpaceOfModule k V).residueField y)) = n := by
    have hcl' : closure (Set.range φ.base) = closure {y} := by
      refine le_antisymm (closure_minimal ?_ isClosed_closure)
        (closure_mono (Set.singleton_subset_iff.mpr ⟨ηU, rfl⟩))
      rintro _ ⟨x, rfl⟩
      have hsp : ηU ⤳ x := (U.ι.isOpenEmbedding.isInducing.specializes_iff (x := ηU)
        (y := x)).mp ((genericPoint_spec X).specializes trivial)
      exact specializes_iff_mem_closure.mp (hsp.map φ.continuous)
    have h := topologicalKrullDim_closure_singleton_eq_trdeg k (projectiveSpaceOfModule k V)
      (projectiveSpaceOfModuleToSpec k V) y
    rw [← hcl', hdim] at h
    exact_mod_cast h.symm
  obtain ⟨v, hv⟩ := exists_algebraicIndependent_coordRatio v₀ hy htr
  let t : ι → (projectiveSpaceOfModule k V).residueField y := fun w =>
    (projectiveSpaceOfModule k V).evaluation D y hy
      ((Proj.awayToSection (grading k V) (coord k v₀)).hom (coordRatio k v₀ w))
  -- the chart ratios as rational functions on `X`
  have hηW' : genericPoint X ∈ U.ι ''ᵁ W := ⟨ηU, hηW, rfl⟩
  let ρ : ι → Γ(X, U.ι ''ᵁ W) := fun w => (U.ι.appIso W).inv
    (φ.appLE D W hle ((Proj.awayToSection (grading k V) (coord k v₀)).hom (coordRatio k v₀ w)))
  have hτ : ∀ w, ratFun (b w) = X.presheaf.germ _ _ hηW' (ρ w) * ratFun (b v₀) := fun w => by
    apply ratFun_eq_germ_mul
    apply restrict_eq_smul_of_pullback
    rw [← hψv, ← hψv]
    exact resTop_eq_appLE_smul k V _ ψ hψ (Finsupp.single v₀ 1) (Finsupp.single w 1) W hWdef hle _
  have hb0 : ratFun (b v₀) ≠ 0 := by
    intro h
    refine b.ne_zero v₀ (ratFun_injective (h.trans ?_))
    exact (map_zero (ofFunctionFieldEquiv (X := X)).symm).symm
  -- the comparison `κ(y) → κ(η)` of residue fields
  let e := (asIso (U.ι.residueFieldMap ηU)).commRingCatIsoToRingEquiv
  let j : (projectiveSpaceOfModule k V).residueField y →+* X.residueField (genericPoint X) :=
    e.symm.toRingHom.comp (φ.residueFieldMap ηU).hom
  have hj : ∀ w, j (t w) = X.residue _ (X.presheaf.germ _ _ hηW' (ρ w)) := by
    intro w
    set g := φ.appLE D W hle
      ((Proj.awayToSection (grading k V) (coord k v₀)).hom (coordRatio k v₀ w))
    have h2 : (φ.residueFieldMap ηU).hom (t w) = U.toScheme.evaluation W ηU hηW g := by
      change (φ.residueFieldMap ηU).hom ((projectiveSpaceOfModule k V).evaluation D (φ ηU) hy
        ((Proj.awayToSection (grading k V) (coord k v₀)).hom (coordRatio k v₀ w))) = _
      rw [Scheme.evaluation_naturality_apply]
      exact (evaluation_map (homOfLE hle) ηU hηW _).symm
    have h3 : (U.ι.residueFieldMap ηU).hom (X.residue _ (X.presheaf.germ _ _ hηW' (ρ w))) =
        U.toScheme.evaluation W ηU hηW g := by
      refine (Scheme.evaluation_naturality_apply U.ι ηU (V := U.ι ''ᵁ W) hηW' (ρ w)).trans ?_
      have h4 := ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_app U.ι W) g
      simp only [ConcreteCategory.comp_apply] at h4
      change U.toScheme.evaluation _ ηU _ (U.ι.app _ ((U.ι.appIso W).inv g)) = _
      rw [h4]
      exact evaluation_map _ ηU _ g
    change e.symm ((φ.residueFieldMap ηU).hom (t w)) = _
    rw [h2, ← h3]
    exact e.symm_apply_apply (X.residue _ (X.presheaf.germ _ _ hηW' (ρ w)))
  letI algX : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation _).hom.toAlgebra
  letI := (kToK f).toAlgebra
  have hover : φ ≫ projectiveSpaceOfModuleToSpec k V = U.ι ≫ f :=
    morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec _ hψ
  have hjk : ∀ r : k, j (algebraMap k _ r) = algebraMap k _ r := by
    intro r
    have h1 : (φ.residueFieldMap ηU).hom (algebraMap k _ r) =
        (U.ι.residueFieldMap ηU).hom (algebraMap k (X.residueField (genericPoint X)) r) := by
      change (φ.residueFieldMap ηU).hom ((projectiveSpaceOfModule k V).Γevaluation (φ ηU)
        ((projectiveSpaceOfModuleToSpec k V).appTop ((Scheme.ΓSpecIso (.of k)).inv r))) =
        (U.ι.residueFieldMap ηU).hom (X.Γevaluation (U.ι ηU) (f.appTop
          ((Scheme.ΓSpecIso (.of k)).inv r)))
      have hc := congrArg (fun g => g.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv r)) hover
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc
      rw [Scheme.Γevaluation_naturality_apply, Scheme.Γevaluation_naturality_apply]
      exact congrArg _ hc
    change e.symm ((φ.residueFieldMap ηU).hom (algebraMap k _ r)) = _
    rw [h1]
    exact e.symm_apply_apply (algebraMap k (X.residueField (genericPoint X)) r)
  let jA : (projectiveSpaceOfModule k V).residueField y →ₐ[k] X.residueField (genericPoint X) :=
    { j with commutes' := hjk }
  let resA : X.functionField →ₐ[k] X.residueField (genericPoint X) :=
    { (X.residue _).hom with commutes' := fun _ => rfl }
  refine ⟨v₀, v, hb0, ?_⟩
  apply AlgebraicIndependent.of_comp resA
  have h1 := hv.map' (f := jA) jA.toRingHom.injective
  convert h1 using 1
  funext l
  change X.residue _ (ratFun (b (v l)) / ratFun (b v₀)) = j (t (v l))
  rw [hj, hτ, mul_div_assoc, div_self hb0, mul_one]

end Image

/-- A projective variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} (hX : IsProjectiveVariety k f) :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have : IsIntegral X := hX.toIsIntegral
  have : AlgebraicGeometry.IsVariety k f := hX.toIsVariety
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp
    (show e ≠ ⊤ by rintro rfl; exact htop he.symm)
  exact ⟨d, he.symm⟩

/-- **A divisor whose linear system has a top-dimensional image is big** (Kollár–Mori 2.60,
(4) ⇒ (1)). Let `X` be a projective variety over `k`, `D` a Cartier divisor on `X` and `m > 0`
an integer. If the image `Y_{𝒪(mD)}` of the morphism `φ_{|mD|}` given by a basis `b` of
`H⁰(X, 𝒪_X(mD))` has the dimension of `X`, then `D` is big. -/
@[mmp "lem_km2c_big_of_image_dimension"]
public theorem isBigCartier_of_topologicalKrullDim_linearSystemImage_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hX : IsProjectiveVariety k f)
    (D : X.CartierDivisor) {m : ℕ} (hm : 0 < m) {ι : Type u}
    (b : letI : X.Over (Spec (.of k)) := ⟨f⟩
      letI := globalSectionsModule k X (MMP.CartierDivisor.sheaf (m • D))
      Module.Basis ι k Γ(MMP.CartierDivisor.sheaf (m • D), ⊤))
    (hY : letI : X.Over (Spec (.of k)) := ⟨f⟩
      letI := globalSectionsModule k X (MMP.CartierDivisor.sheaf (m • D))
      topologicalKrullDim (linearSystemImage k (MMP.CartierDivisor.sheaf (m • D)) b) =
        topologicalKrullDim X) :
    IsBigCartier k f D := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsProper f := isProper_of_isProjectiveMorphism f hX.isProjective
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq hX
  rw [hn] at hY
  obtain ⟨v₀, v, h₀, hind⟩ := exists_algebraicIndependent_ratio f hX (m • D) b hY
  refine isBigCartier_of_growth f hX D hn (growth_of_pow_le f D hm fun j => ?_)
  have := pow_le_cartierH0 f (m • D) (b v₀) (fun l => b (v l)) h₀ hind j
  rwa [← mul_smul] at this

/-! ### Nef and big divisors -/

section NefBig

/-- Additivity of the intersection number in one slot, for a slot replaced by a tensor product. -/
private theorem intersectionNumber_update_of_iso_tensorObj (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (q : Fin d)
    (P P' P'' : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P']
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P'']
    (e : P ≅ Scheme.Modules.tensorObj P' P'') :
    haveI := isInvertible_update G q P
    haveI := isInvertible_update G q P'
    haveI := isInvertible_update G q P''
    intersectionNumber k f i d hd (Function.update G q P) =
      intersectionNumber k f i d hd (Function.update G q P') +
        intersectionNumber k f i d hd (Function.update G q P'') := by
  haveI := isInvertible_update G q P
  haveI := isInvertible_update G q P'
  haveI := isInvertible_update G q P''
  refine intersectionNumber_tensor k f i d hd q _ _ _
    (fun r hr => by rw [Function.update_of_ne hr, Function.update_of_ne hr])
    (fun r hr => by rw [Function.update_of_ne hr, Function.update_of_ne hr]) ?_
  rw [Function.update_self, Function.update_self, Function.update_self]
  exact e

/-- The intersection number depends on one slot only through its isomorphism class. -/
private theorem intersectionNumber_update_of_iso (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (q : Fin d)
    (P P' : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P'] (e : P ≅ P') :
    haveI := isInvertible_update G q P
    haveI := isInvertible_update G q P'
    intersectionNumber k f i d hd (Function.update G q P) =
      intersectionNumber k f i d hd (Function.update G q P') := by
  haveI := isInvertible_update G q P
  haveI := isInvertible_update G q P'
  exact intersectionNumber_eq_of_iso_at k f i d hd _ _ q
    (fun r hr => by rw [Function.update_of_ne hr, Function.update_of_ne hr])
    (eqToIso (Function.update_self q P G) ≪≫ e ≪≫ eqToIso (Function.update_self q P' G).symm)

/-- Replacing a slot `𝒪_X(D)` by `𝒪_X(mD)`, `m ≥ 1`, multiplies the intersection number by `m`. -/
private theorem intersectionNumber_update_sheaf_nsmul (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (q : Fin d)
    (D : X.CartierDivisor) (hG : G q = MMP.CartierDivisor.sheaf D) {m : ℕ} (hm : 1 ≤ m) :
    haveI := isInvertible_update G q (MMP.CartierDivisor.sheaf (m • D))
    intersectionNumber k f i d hd
        (Function.update G q (MMP.CartierDivisor.sheaf (m • D))) =
      m * intersectionNumber k f i d hd G := by
  induction m, hm using Nat.le_induction with
  | base =>
    haveI := isInvertible_update G q (MMP.CartierDivisor.sheaf (1 • D))
    rw [Nat.cast_one, one_mul]
    exact intersectionNumber_congr_family k f i d hd
      (by rw [one_smul, ← hG, Function.update_eq_self])
  | succ m hm ih =>
    haveI := isInvertible_update G q (MMP.CartierDivisor.sheaf (m • D))
    haveI := isInvertible_update G q (MMP.CartierDivisor.sheaf ((m + 1) • D))
    haveI := isInvertible_update G q (MMP.CartierDivisor.sheaf D)
    rw [intersectionNumber_update_of_iso_tensorObj k f i d hd G q _
      (MMP.CartierDivisor.sheaf (m • D)) (MMP.CartierDivisor.sheaf D)
      (eqToIso (congrArg MMP.CartierDivisor.sheaf (succ_nsmul D m)) ≪≫
        (MMP.CartierDivisorSheaf.sheafMulIso (m • D) D).symm), ih,
      intersectionNumber_congr_family k f i d hd (by rw [← hG, Function.update_eq_self] :
        Function.update G q (MMP.CartierDivisor.sheaf D) = G)]
    push_cast
    ring

/-- **A slot of an effective divisor gives a nonnegative number.** On a projective variety of
dimension at most `d`, `d ≥ 1`, with `L` nef and `M` ample, the intersection number of a family
of `d` sheaves with `𝒪_X(E)`, `E` effective, in one slot and `L` or `M` in the others is
nonnegative. -/
private theorem intersectionNumber_nonneg_of_eq_sheaf_of_isEffective (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX : IsProjectiveVariety k f)
    (L M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (hL : IsNef k f L)
    (hM : Stacks.Ample.IsAmple X M) (d : ℕ) (hd0 : 0 < d) (hd : topologicalKrullDim X ≤ d)
    (E : X.CartierDivisor) (hE : MMP.Intersection.IsEffective E)
    (G : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)]
    (q₀ : Fin d) (hq₀ : G q₀ = MMP.CartierDivisor.sheaf E)
    (hG : ∀ q, q ≠ q₀ → G q = L ∨ G q = M) :
    0 ≤ intersectionNumber k f (𝟙 X) d hd G := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  let σ : Equiv.Perm (Fin (d + 1)) := Equiv.swap 0 q₀
  rw [← intersectionNumber_comp_perm k f (𝟙 X) (d + 1) hd G σ,
    ← MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    MMP.Mori.sheafIntersectionNumber_eq_of_isEffective k f (𝟙 X) d hd (fun j => G (σ j)) E
      hE
      ((Scheme.Modules.pullbackId X).app _ ≪≫ eqToIso (by simp [σ, hq₀])),
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple_of_forall_eq_or_eq k f L M hM
    (fun j W i _ _ hW => ?_) _ d _ _ (fun t => hG _ ?_)
  · have h := MMP.Mori.sheafSelfIntersectionNumber_nonneg_of_isNef k f hX L hL W i hW
    unfold MMP.Mori.sheafSelfIntersectionNumber at h
    rwa [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h
  · rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero t

/-- **The step `m aⱼ ≥ aⱼ₊₁`.** Let `𝒪_X(mD) ≅ 𝒪_X(A + E)` with `m ≥ 1`, `𝒪_X(D)` nef, `𝒪_X(A)`
ample and `E` effective. In a family of `d ≥ 1` sheaves with `𝒪_X(D)` in the slot `q₀` and
`𝒪_X(D)` or `𝒪_X(A)` in every other slot, replacing the slot `q₀` by `𝒪_X(A)` multiplies the
intersection number by at most `m`. -/
private theorem intersectionNumber_update_ample_le_mul (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX : IsProjectiveVariety k f)
    (D A E : X.CartierDivisor) (hD : IsNef k f (MMP.CartierDivisor.sheaf D))
    (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A))
    (hE : MMP.Intersection.IsEffective E) {m : ℕ} (hm : 1 ≤ m)
    (φ : MMP.CartierDivisor.sheaf (m • D) ≅ MMP.CartierDivisor.sheaf (A + E))
    (d : ℕ) (hd0 : 0 < d) (hd : topologicalKrullDim X ≤ d) (G : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)] (q₀ : Fin d)
    (hq₀ : G q₀ = MMP.CartierDivisor.sheaf D)
    (hG : ∀ q, q ≠ q₀ → G q = MMP.CartierDivisor.sheaf D ∨
      G q = MMP.CartierDivisor.sheaf A) :
    haveI := isInvertible_update G q₀ (MMP.CartierDivisor.sheaf A)
    intersectionNumber k f (𝟙 X) d hd
        (Function.update G q₀ (MMP.CartierDivisor.sheaf A)) ≤
      m * intersectionNumber k f (𝟙 X) d hd G := by
  haveI := isInvertible_update G q₀ (MMP.CartierDivisor.sheaf (m • D))
  haveI := isInvertible_update G q₀ (MMP.CartierDivisor.sheaf (A + E))
  haveI := isInvertible_update G q₀ (MMP.CartierDivisor.sheaf A)
  haveI := isInvertible_update G q₀ (MMP.CartierDivisor.sheaf E)
  rw [← intersectionNumber_update_sheaf_nsmul k f (𝟙 X) d hd G q₀ D hq₀ hm,
    intersectionNumber_update_of_iso k f (𝟙 X) d hd G q₀ _ _ φ,
    intersectionNumber_update_of_iso_tensorObj k f (𝟙 X) d hd G q₀ _ _ _
      (MMP.CartierDivisorSheaf.sheafMulIso A E).symm]
  refine le_add_of_nonneg_right
    (intersectionNumber_nonneg_of_eq_sheaf_of_isEffective k f hX _ _ hD hA d hd0 hd E hE _ q₀
      (Function.update_self _ _ _) fun r hr => ?_)
  rw [Function.update_of_ne hr]
  exact hG r hr

/-- **Kodaira's lemma, in sheaf form**: for a big Cartier divisor `D` on a projective variety
there are `m ≥ 1`, `A` with `𝒪_X(A)` ample and `E` effective with `𝒪_X(mD) ≅ 𝒪_X(A + E)`. -/
private theorem exists_sheaf_nsmul_iso_add {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hX : IsProjectiveVariety k f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : X.CartierDivisor) (hbig : IsBigCartier k f D) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ A E : X.CartierDivisor,
      Scheme.Modules.IsAmple X (MMP.CartierDivisor.sheaf A) ∧
      MMP.Intersection.IsEffective E ∧
      Nonempty (MMP.CartierDivisor.sheaf (m • D) ≅ MMP.CartierDivisor.sheaf (A + E)) := by
  obtain ⟨m, hm, A, E, -, hAmp, hE, hlin⟩ :=
    MMP.Mori.exists_linearlyEquivalent_ample_add_effective f hX hn D (by
      obtain ⟨n', hn', c, hc, k₀, hk⟩ := hbig
      obtain rfl : n' = n := by exact_mod_cast hn'.symm.trans hn
      refine ⟨c, hc, Set.infinite_of_forall_exists_gt fun a => ⟨max a k₀.toNat + 1, ?_, by omega⟩⟩
      have h := hk ((max a k₀.toNat + 1 : ℕ) : ℤ) (by omega)
      rwa [natCast_zsmul, Int.cast_natCast] at h)
  obtain ⟨φ⟩ := MMP.CartierDivisor.nonempty_iso_of_linearlyEquivalent hlin
  exact ⟨m, hm, A, E, (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).2 hAmp, hE,
    ⟨φ⟩⟩

/-- The family `(L, …, L, M, …, M)` of `n` sheaves with `j` copies of `L`. -/
private def mixedFamily {X : Scheme} (L M : X.Modules) (n j : ℕ) : Fin n → X.Modules :=
  fun q => if (q : ℕ) < j then L else M

private theorem isInvertible_mixedFamily {X : Scheme} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (n j : ℕ) (q : Fin n) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (mixedFamily L M n j q) := by
  unfold mixedFamily
  split_ifs <;> infer_instance

private theorem update_mixedFamily {X : Scheme} (L M : X.Modules) {n j : ℕ} (hj : j < n) :
    Function.update (mixedFamily L M n j) ⟨j, hj⟩ L = mixedFamily L M n (j + 1) := by
  funext r
  simp only [mixedFamily, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- Iterating `aⱼ₊₁ ≤ m aⱼ` gives `aₙ ≤ mⁿ a₀`. -/
private theorem le_pow_mul_of_forall_lt_le_mul {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {a : ℕ → R} {m : R} (hm : 0 ≤ m) {n : ℕ}
    (h : ∀ j < n, a (j + 1) ≤ m * a j) : a n ≤ m ^ n * a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a (n + 1) ≤ m * a n := h n n.lt_succ_self
      _ ≤ m * (m ^ n * a 0) := mul_le_mul_of_nonneg_left (ih fun j hj => h j (by omega)) hm
      _ = m ^ (n + 1) * a 0 := by ring

end NefBig

/-- **Nef and big implies positive top self-intersection** (Kollár–Mori 2.61 (1) ⇒ (2)). On a
projective variety `X` of dimension `n` over `k`, a Cartier divisor `D` whose invertible sheaf
`𝒪_X(D)` is nef and which is big satisfies `(Dⁿ) > 0`. -/
@[mmp "lem_km2c_nef_big_top_positive"]
public theorem sheafSelfIntersectionNumber_pos_of_isNef_of_isBigCartier {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : X.CartierDivisor)
    (hnef : IsNef k f (MMP.CartierDivisor.sheaf D)) (hbig : IsBigCartier k f D) :
    0 < sheafSelfIntersectionNumber k f (𝟙 X) n hn.le (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨m, hm, A, E, hA, hE, ⟨φ⟩⟩ := exists_sheaf_nsmul_iso_add f inferInstance hn D hbig
  set LA := MMP.CartierDivisor.sheaf A
  set LD := MMP.CartierDivisor.sheaf D
  haveI := isInvertible_mixedFamily LA LD n
  -- `aⱼ = (Aʲ · Dⁿ⁻ʲ)`
  let a : ℕ → ℤ := fun j => intersectionNumber k f (𝟙 X) n hn.le (mixedFamily LA LD n j)
  have hstep : ∀ j < n, a (j + 1) ≤ m * a j := fun j hj => by
    haveI := isInvertible_update (mixedFamily LA LD n j) ⟨j, hj⟩ LA
    refine (intersectionNumber_congr_family k f (𝟙 X) n hn.le
      (update_mixedFamily LA LD hj)).symm.trans_le
      (intersectionNumber_update_ample_le_mul k f inferInstance D A E hnef
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X LA).1 hA) hE hm φ n (by omega)
        hn.le _ ⟨j, hj⟩ (by simp [mixedFamily, LD]) fun q _ => by
          unfold mixedFamily; split_ifs; exacts [Or.inr rfl, Or.inl rfl])
  have hpos : 0 < a n := (selfIntersectionNumber_pos k f (𝟙 X) n hn LA hA).trans_eq
    (intersectionNumber_congr_family k f (𝟙 X) n hn.le (funext fun q => by simp [mixedFamily]))
  unfold MMP.Mori.sheafSelfIntersectionNumber
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_congr_family k f (𝟙 X) n hn.le
      (show (fun _ => LD) = mixedFamily LA LD n 0 by funext q; simp [mixedFamily])]
  exact pos_of_mul_pos_right (hpos.trans_le (le_pow_mul_of_forall_lt_le_mul (by positivity) hstep))
    (by positivity)

end MMP.Mori
