module

public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeContraction
public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor

/-!
# Numerical divisor classes along elementary klt steps

Let `(X, C)` be a projective `ℚ`-factorial klt pair with rational boundary, `K` a canonical
divisor, `R` a `(K + C)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Z` its contraction.
Consider an elementary step `X ⟶ Z ⟵ X⁺` with `X⁺` a projective `ℚ`-factorial normal variety:
either `f` is divisorial and `f⁺ : X⁺ ⟶ Z` is an isomorphism, or `f⁺` is a flip of `f`. The
transform `D ↦ (f⁺)⁻¹_* f_* D` of `ℝ`-divisors (the pushforward in the divisorial case, the strict
transform in the flip case) sends `ℝ`-Cartier divisors to `ℝ`-Cartier divisors and numerically
trivial ones to numerically trivial ones, absolutely and over any projective base `S` over which
the step is taken. Every `ℝ`-Cartier divisor on `X⁺` is the transform of an `ℝ`-Cartier divisor
on `X`, so the induced map `N¹(X)_ℝ → N¹(X⁺)_ℝ` is surjective, and so is `N¹(X/S)_ℝ → N¹(X⁺/S)_ℝ`;
in particular the transforms of a finite family spanning `N¹(X)_ℝ` span `N¹(X⁺)_ℝ`, and the
members with zero transform may be dropped.

## Main results

* `MMP.Fourfold.IsKltPair.isNumericallyTrivialOver_flipTransform_of_isContractionOfRay`.

## Implementation notes

Real divisors are Weil `ℝ`-divisors `MMP.Mori.RDivisor`; `ℝ`-Cartier is
`MMP.Flips.IsCartierCombination`, and numerical triviality and equivalence over a base `T` are
`MMP.Flips.IsNumericallyTrivialOver` and `MMP.Flips.IsNumericallyEquivalentOver` along the
structure map to `T`, the absolute notions being those over `Spec k`. A class of `N¹` is thus the
numerical class of an `ℝ`-Cartier `ℝ`-divisor, and the surjectivity of `N¹(X)_ℝ → N¹(X⁺)_ℝ` is
stated on representatives, in the stronger form that every `ℝ`-Cartier divisor on `X⁺` is exactly
a transform; this form does not depend on the base. Both kinds of step are written
`X ⟶ Z ⟵ X⁺` with the transform `MMP.Mori.flipTransform f f⁺`; a divisorial step has `f⁺` an
isomorphism, so that its transform is the pushforward `f_*`. The base field is any field `k`,
the klt condition forcing it to be algebraically closed of characteristic zero.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7, 3.36,
  3.37
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/- ### Real numbers as integral combinations of `ℤ`-independent ones -/

/-- Finitely many real numbers `r₁, …, r_m` are integral combinations `rⱼ = ∑ₗ zₗⱼ bₗ` of finitely
many `ℤ`-linearly independent real numbers `bₗ`: a basis of the free abelian group they
generate. -/
private theorem exists_intCombination {m : ℕ} (r : Fin m → ℝ) :
    ∃ (n : ℕ) (b : Fin n → ℝ) (z : Fin n → Fin m → ℤ),
      (∀ j, r j = ∑ l, (z l j : ℝ) * b l) ∧
        ∀ c : Fin n → ℤ, ∑ l, (c l : ℝ) * b l = 0 → ∀ l, c l = 0 := by
  let M : Submodule ℤ ℝ := Submodule.span ℤ (Set.range r)
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ (Set.finite_range r)
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let B := (Module.Free.chooseBasis ℤ M).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ M))
  have hmem : ∀ j, r j ∈ M := fun j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨_, fun l => (B l : ℝ), fun l j => B.repr ⟨r j, hmem j⟩ l, fun j => ?_, fun c hc => ?_⟩
  · have h := congrArg Subtype.val (B.sum_repr ⟨r j, hmem j⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, zsmul_eq_mul] at h
    exact h.symm
  · have h0 : ∑ l, c l • B l = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [Submodule.coe_smul, zsmul_eq_mul, Submodule.coe_zero] using hc
    exact Fintype.linearIndependent_iff.mp B.linearIndependent c h0

/- ### The strict transform on real divisors -/

section Transform

variable {X Z X' : Scheme.{0}}

/-- `mapPrimeDivisors` commutes with a change of coefficients along an additive map. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {Y : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (g : R →+ S)
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapCoeffsAddMonoidHom g (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add A B hA hB => simp only [map_add, hA, hB]
  | single E n =>
    have h1 : ∀ {W : Scheme.{0}} (F : MMP.Mori.PrimeDivisor W) (a : R),
        DivisorWithCoeffs.mapCoeffsAddMonoidHom g (Finsupp.single F a) = Finsupp.single F (g a) :=
      fun F a => by
        simp [DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply, DivisorWithCoeffs.mapCoeffs]
    rw [h1, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E
    · simp only [Option.elim, map_zero]
    · simp only [Option.elim, Finsupp.singleAddHom_apply, h1]

/-- The strict transform commutes with regarding a divisor as an `ℝ`-divisor. -/
private theorem toRDivisor_flipTransform (f : X ⟶ Z) (fp : X' ⟶ Z) (D : Divisor X) :
    Divisor.toRDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toRDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, Divisor.toRDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- The strict transform of real divisors is `ℝ`-linear. -/
private theorem flipTransform_smul (f : X ⟶ Z) (fp : X' ⟶ Z) (a : ℝ) (D : RDivisor X) :
    flipTransform f fp (a • D) = a • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

/-- The strict transform of a finite real combination. -/
private theorem flipTransform_sum_smul (f : X ⟶ Z) (fp : X' ⟶ Z) {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (D : ι → RDivisor X) :
    flipTransform f fp (∑ i ∈ s, a i • D i) = ∑ i ∈ s, a i • flipTransform f fp (D i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => flipTransform_smul f fp (a i) (D i)

end Transform

/- ### `ℝ`-Cartier divisors and numerical triviality -/

section Numerical

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor `P` has a
Cartier multiple `mP`, and `a P = (a / m) (mP)`. -/
private theorem isCartierCombination_of_isQFactorial {k : Type} [Field k]
    {sX : X ⟶ Spec (.of k)} (hQ : IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  induction D using Finsupp.induction_linear with
  | zero => exact MMP.Fourfold.Oai4C1.Negativity.isCartierCombination_zero
  | add A B hA hB => exact MMP.Flips.isCartierCombination_add hA hB
  | single P a =>
    obtain ⟨m, hm, hc⟩ := hQ.2 (Finsupp.single P 1)
    refine ⟨1, fun _ => a / m, fun _ => (m : ℤ) • Finsupp.single P 1, fun _ => hc, ?_⟩
    refine Finsupp.ext fun Q => ?_
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [Finset.univ_unique, Finset.sum_singleton, Finsupp.smul_apply, smul_eq_mul,
      DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply]
    classical
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · push_cast
      field_simp
    · simp

variable {k : Type} [Field k] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {Y : Scheme.{0}}

/-- The empty presentation of the zero divisor computes the intersection number `0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 C 0 :=
  ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩

/-- `N` is numerically trivial over `g` iff it is `ℝ`-Cartier and every value of `N · C`
vanishes for the curves `C` contracted by `g`. -/
private theorem isNumericallyTrivialOver_iff {g : X ⟶ Y} {N : RDivisor X} :
    IsNumericallyTrivialOver k sX g N ↔ IsCartierCombination N ∧
      ∀ C : ProperCurve sX, C.IsContractedBy g → ∀ (m : ℕ) (r : Fin m → ℝ)
        (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber k sX N r L C x → x = 0 := by
  refine ⟨fun h => ⟨h.1, fun C hC m r L x hx => ?_⟩,
    fun h => ⟨h.1, MMP.Fourfold.Oai4C1.Negativity.isCartierCombination_zero,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩⟩
  · exact h.2.2 C hC m r L x 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)
  · rw [h.2 C hC _ _ _ _ hx₁, (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₂
      (isRIntersectionNumber_zero C)]

/-- An `ℝ`-Cartier divisor has a presentation by Cartier divisors written with
`Divisor.toRDivisor`. -/
private theorem exists_eq_sum_toRDivisor {N : RDivisor X} (h : IsCartierCombination N) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (_ : ∀ j, (L j).IsCartier),
      N = ∑ j, r j • Divisor.toRDivisor (L j) := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact ⟨m, r, L, hL, by simp only [toRDivisor_eq_mapCoeffs]⟩

/-- An `ℝ`-Cartier divisor is a combination `∑ₗ bₗ Dₗ` of Cartier divisors `Dₗ` with
coefficients `bₗ` linearly independent over `ℤ`. -/
private theorem exists_eq_sum_toRDivisor_of_intIndependent {N : RDivisor X}
    (h : IsCartierCombination N) :
    ∃ (n : ℕ) (b : Fin n → ℝ) (D : Fin n → Divisor X) (_ : ∀ l, (D l).IsCartier),
      N = ∑ l, b l • Divisor.toRDivisor (D l) ∧
        ∀ c : Fin n → ℤ, ∑ l, (c l : ℝ) * b l = 0 → ∀ l, c l = 0 := by
  obtain ⟨m, r, L, hL, rfl⟩ := exists_eq_sum_toRDivisor h
  obtain ⟨n, b, z, hrz, hind⟩ := exists_intCombination r
  refine ⟨n, b, fun l => ∑ j, z l j • L j, fun l => Finset.sum_induction _ Divisor.IsCartier
    (fun _ _ h h' => h.add h') Divisor.isCartier_zero fun j _ => (hL j).zsmul _, ?_, hind⟩
  simp only [map_sum, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hrz j, Finset.sum_smul]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]

/-- `N₁ ≡_g N₂` for `ℝ`-Cartier `N₁, N₂` with `N₁ - N₂ ≡_g 0`. -/
private theorem isNumericallyEquivalentOver_of_sub {g : X ⟶ Y} {N₁ N₂ : RDivisor X}
    (h₁ : IsCartierCombination N₁) (h₂ : IsCartierCombination N₂)
    (h : IsNumericallyTrivialOver k sX g (N₁ - N₂)) : IsNumericallyEquivalentOver k sX g N₁ N₂ := by
  refine ⟨h₁, h₂, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩
  have hlin := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hlin
  have := (isNumericallyTrivialOver_iff.mp h).2 C hC _ _ _ _ hlin
  linarith

/-- `N₁ ≡_g N₂` implies `N₁ - N₂ ≡_g 0`. -/
private theorem isNumericallyTrivialOver_sub {g : X ⟶ Y} {N₁ N₂ : RDivisor X}
    (h : IsNumericallyEquivalentOver k sX g N₁ N₂) : IsNumericallyTrivialOver k sX g (N₁ - N₂) := by
  obtain ⟨h₁, h₂, h⟩ := h
  have hc : IsCartierCombination (N₁ - N₂) := by
    rw [sub_eq_add_neg]
    refine MMP.Flips.isCartierCombination_add h₁ ?_
    obtain ⟨m, r, L, hL, rfl⟩ := h₂
    exact ⟨m, -r, L, hL, by simp [Finset.sum_neg_distrib, neg_smul]⟩
  refine isNumericallyTrivialOver_iff.mpr ⟨hc, fun C hC m r L x hx => ?_⟩
  obtain ⟨m₁, r₁, L₁, hL₁, e₁⟩ := exists_eq_sum_toRDivisor h₁
  obtain ⟨m₂, r₂, L₂, hL₂, e₂⟩ := exists_eq_sum_toRDivisor h₂
  have hx₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
  have hx₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
  rw [← e₁] at hx₁
  rw [← e₂] at hx₂
  have hlin := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hlin
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hlin,
    h C hC _ _ _ _ _ _ _ _ hx₁ hx₂]
  ring

end Numerical

/- ### Curves under a morphism -/

section Curves

variable {k : Type} [Field k]

/-- A nonempty fibre of a map out of a Noetherian `T₀` space has a point closed in the fibre. -/
private theorem exists_closed_mem_fiber {A B : Type*} [TopologicalSpace A] [T0Space A]
    [TopologicalSpace.NoetherianSpace A] (f : A → B) {y : B} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private theorem topologicalKrullDim_eq_zero_of_subsingleton (A : Type*) [TopologicalSpace A]
    [Nonempty A] [Subsingleton A] : topologicalKrullDim A = 0 := by
  have : DiscreteTopology A := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty A›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds A) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over the base field: it factors through its scheme-theoretic image, which is `C'`. -/
private theorem isProper_comp_of_closure_range {A B : Scheme.{0}} {sB : B ⟶ Spec (.of k)}
    (C' : ProperCurve sB) (φ : A ⟶ B) [IsReduced A] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {C'.point}) : IsProper (φ ≫ sB) := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {C'.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB); rw [hker]; exact C'.isProper_ι_comp
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting proper curves.** Let `h : A ⟶ B` be a proper surjective morphism of schemes of
finite type over `k`. Every proper curve `C'` of `B` is the image of a proper curve `C` of `A`:
`h` maps the generic point of `C` to that of `C'`, and `h(C) = C'`. -/
private theorem exists_properCurve_map_eq_image_closure {A B : Scheme.{0}} (sA : A ⟶ Spec (.of k))
    (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] (h : A ⟶ B) [IsProper h] [Surjective h]
    (hh : h ≫ sB = sA) (C' : ProperCurve sB) :
    ∃ C : ProperCurve sA, h.base C.point = C'.point ∧
      h.base '' closure {C.point} = closure {C'.point} := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base (h.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = C'.point → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  refine ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range C' φ hclr⟩, haξ, ?_⟩
  rw [← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton, haξ]

/-- The generic point of a proper curve is not a closed point. -/
private theorem ProperCurve.closure_point_ne_singleton {B : Scheme.{0}} {sB : B ⟶ Spec (.of k)}
    (C : ProperCurve sB) : closure {C.point} ≠ ({C.point} : Set B) := by
  intro hcl
  have hsub : Subsingleton (curveSubschemeAt C.point) := by
    refine ⟨fun a b => (curveSubschemeAtι C.point).isClosedEmbedding.injective ?_⟩
    have hmem : ∀ d, (curveSubschemeAtι C.point).base d = C.point := by
      intro d
      have : (curveSubschemeAtι C.point).base d ∈
          Set.range (curveSubschemeAtι C.point).base := ⟨d, rfl⟩
      rwa [range_curveSubschemeAtι, hcl] at this
    rw [hmem a, hmem b]
  exact Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim C.dim_eq.ge hsub

end Curves

/- ### Contractions over the base point -/

section BasePoint

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Over the base point, the natural map `N₁(X / Spec k) → N₁(X)` is bijective. -/
private theorem bijective_relativeToAbsolute :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => fun _ _ => Subsingleton.elim _ _
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- The target of a morphism from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is integral. -/
private theorem isIntegral_of_isIso_app {Z : Scheme.{0}} [IsIntegral X] (ψ : X ⟶ Z)
    (hψ : ∀ V : Z.Opens, IsIso (ψ.app V)) : IsIntegral Z where
  nonempty := ⟨ψ (Nonempty.some inferInstance)⟩
  component_integral V _ := by
    have hne : Nonempty (ψ ⁻¹ᵁ V) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have hbot : ψ ⁻¹ᵁ V = ⊥ := by
        ext x
        simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne.false ⟨x, hx⟩
      haveI := Scheme.component_nontrivial Z V
      haveI := hψ V
      haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by rw [hbot]; infer_instance
      obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
      exact hab ((ConcreteCategory.bijective_of_isIso (ψ.app V)).1 (Subsingleton.elim _ _))
    haveI := hψ V
    exact Function.Injective.isDomain (ψ.app V).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app V)).1

end BasePoint

/- ### Changing the structure morphism by an automorphism of the base field -/

section Twist

variable {k : Type} [Field k]

/-- Restricting scalars along `φ ∘ τ`, for an automorphism `τ` of `k`, does not change the
dimension over `k`. -/
private theorem finrank_restrictScalars_comp_ringEquiv {A : Type} [CommRing A] (φ : k →+* A)
    (τ : k ≃+* k) (M : ModuleCat.{0} A) :
    Module.finrank k ((ModuleCat.restrictScalars (φ.comp τ.toRingHom)).obj M) =
      Module.finrank k ((ModuleCat.restrictScalars φ).obj M) := by
  have := lift_rank_eq_of_equiv_equiv (R := k) (R' := k)
    (M := (ModuleCat.restrictScalars (φ.comp τ.toRingHom)).obj M)
    (M' := (ModuleCat.restrictScalars φ).obj M) τ (AddEquiv.refl _) τ.bijective (fun r m => by
      simp only [AddEquiv.refl_apply, ModuleCat.restrictScalars.smul_def, RingHom.comp_apply]
      rfl)
  simp only [Cardinal.lift_id] at this
  exact congrArg Cardinal.toNat this

/-- The ring map `k → Γ(Y, 𝒪_Y)` of a structure morphism `π : Y ⟶ Spec k`. -/
private noncomputable abbrev structureRingHom {Y : Scheme.{0}} (π : Y ⟶ Spec (.of k)) :
    k →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop).hom

/-- The degree of an invertible sheaf on a proper curve is unchanged when the structure morphism
is twisted by an automorphism `τ` of `k`: the cohomology groups are the same groups, with `k`
acting through `τ`. -/
private theorem invertibleCurveDegree_eq_of_structureRingHom_eq {Y : Scheme.{0}}
    {π π' : Y ⟶ Spec (.of k)} [IsProper π] [IsProper π'] (τ : k ≃+* k)
    (h : structureRingHom π' = (structureRingHom π).comp τ.toRingHom)
    (hdim : topologicalKrullDim Y ≤ 1) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    invertibleCurveDegree k π' hdim L = invertibleCurveDegree k π hdim L := by
  have happ : ∀ t : Y ⟶ Spec (.of k), ((Scheme.ΓSpecIso (.of k)).inv ≫
      t.appLE ⊤ ⊤ (by simp)).hom = structureRingHom t := fun t => by
    rw [structureRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have key : ∀ (F : Y.Modules) (n : ℕ), Module.finrank k (cohomologyOverField k π' F n) =
      Module.finrank k (cohomologyOverField k π F n) := by
    intro F n
    unfold cohomologyOverField
    rw [happ, happ, h]
    exact finrank_restrictScalars_comp_ringEquiv _ τ _
  unfold invertibleCurveDegree
  congr 1 <;> exact finsum_congr fun n => congrArg _ (congrArg _ (key _ n))

/-- Two structure morphisms of an integral scheme proper over an algebraically closed field
differ by an automorphism of the field: both identify `k` with `Γ(X, 𝒪_X)`. -/
private theorem exists_structureRingHom_eq_comp [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
    (s s' : X ⟶ Spec (.of k)) [IsProper s] [IsProper s'] :
    ∃ τ : k ≃+* k, structureRingHom s' = (structureRingHom s).comp τ.toRingHom := by
  have hbij : ∀ (t : X ⟶ Spec (.of k)) [IsProper t], Function.Bijective (structureRingHom t) := by
    intro t _
    letI : Algebra k Γ(X, ⊤) := (structureRingHom t).toAlgebra
    have hint : (structureRingHom t).IsIntegral :=
      RingHom.IsIntegral.trans _ _
        (RingHom.isIntegral_of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
        (isIntegral_appTop_of_universallyClosed t)
    have : Algebra.IsIntegral k Γ(X, ⊤) := ⟨hint⟩
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  refine ⟨(RingEquiv.ofBijective _ (hbij s')).trans (RingEquiv.ofBijective _ (hbij s)).symm,
    RingHom.ext fun x => ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.trans_apply]
  exact ((RingEquiv.ofBijective _ (hbij s)).apply_symm_apply _).symm

/-- Numerical equivalence over `g` is unchanged when the structure morphism of `X` is replaced by
one giving every invertible sheaf the same degree on every proper curve. -/
private theorem isNumericallyEquivalentOver_of_degreeOn_eq {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of k)} [IsProper s]
    [IsProper s']
    (hdeg : ∀ {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ s)] [IsProper (i ≫ s')]
      (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      degreeOn k s' i hdim L = degreeOn k s i hdim L)
    {g : X ⟶ Y} {N₁ N₂ : RDivisor X} (h : IsNumericallyEquivalentOver k s g N₁ N₂) :
    IsNumericallyEquivalentOver k s' g N₁ N₂ := by
  refine ⟨h.1, h.2.1, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩
  let C₀ : ProperCurve s := ⟨C.point, C.dim_eq, inferInstance⟩
  have htr : ∀ {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ},
      IsRIntersectionNumber k s' D r L C x → IsRIntersectionNumber k s D r L C₀ x := by
    rintro D m r L x ⟨hL, d, hD, hd, hx⟩
    refine ⟨hL, d, hD, fun j => ?_, hx⟩
    obtain ⟨C', ν, hν, hdim, hdj⟩ := hd j
    refine ⟨C', ν, hν, hdim, ?_⟩
    have := hν.isFinite
    have : IsProper ((ν ≫ C.ι) ≫ s) := by rw [Category.assoc]; infer_instance
    have : IsProper ((ν ≫ C.ι) ≫ s') := by rw [Category.assoc]; infer_instance
    rw [hdj]
    have := QuasiCompact.compactSpace_of_compactSpace s
    have := (hL j).isInvertibleModule_divisorialSheaf
    exact hdeg (ν ≫ C.ι) hdim _
  exact h.2.2 C₀ hC _ _ _ _ _ _ _ _ (htr hx₁) (htr hx₂)

/-- On an integral scheme proper over an algebraically closed field, numerical equivalence over
`g` does not depend on the structure morphism. -/
private theorem isNumericallyEquivalentOver_of_isAlgClosed [IsAlgClosed k] {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of k)}
    [IsProper s] [IsProper s'] {g : X ⟶ Y} {N₁ N₂ : RDivisor X}
    (h : IsNumericallyEquivalentOver k s g N₁ N₂) : IsNumericallyEquivalentOver k s' g N₁ N₂ := by
  obtain ⟨τ, hτ⟩ := exists_structureRingHom_eq_comp s s'
  refine isNumericallyEquivalentOver_of_degreeOn_eq (fun {C} i _ _ hdim L _ => ?_) h
  refine invertibleCurveDegree_eq_of_structureRingHom_eq τ ?_ hdim _
  refine RingHom.ext fun x => ?_
  simp only [structureRingHom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg i.appTop.hom (RingHom.congr_fun hτ x)

end Twist

/- ### Descent along the contraction -/

/-- Over the base point, a negative extremal ray `R` of `NE̅(X)` pulls back along
`N₁(X / Spec k) ≅ N₁(X)` to a negative extremal face of `NE̅(X / Spec k)`, whose curves are those
contracted by the contraction `f` of `R`. -/
private theorem isNegativeExtremalFace_preimage_relativeToAbsolute {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX]
    [AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k)))] {D : QDivisor X}
    (hD : D.IsQCartier) {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hR : IsNegativeExtremalRayOf sX D R) (hf : IsContractionOfRay sX sZ R f) :
    IsNegativeExtremalFace ℝ
        (relativeClosedConeOfCurves sX sX : Set (RelativeNumericalCurveClasses sX sX))
        ((MMP.Fourfold.QDivisor.curveForm sX D hD).comp (relativeToAbsolute sX sX))
        (relativeToAbsolute sX sX ⁻¹' R) ∧
      ∀ (A : ProperCurve sX) (hA : A.IsContractedBy sX),
        A.relativeClass sX hA ∈ relativeToAbsolute sX sX ⁻¹' R ↔ A.IsContractedBy f := by
  set e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) (bijective_relativeToAbsolute sX)
  have hNimg : e '' (relativeClosedConeOfCurves sX sX : Set _) =
      (closedConeOfCurves sX : Set _) := by
    have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of k))) sX
      (Category.comp_id sX)
    rwa [(bijective_relativeToAbsolute sX).2.range_eq, Set.inter_univ] at this
  have hNpre : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← hNimg, ← Set.image_comp]
    simp
  obtain ⟨_, hRay, hneg⟩ := hR
  have hFray : IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _) (e ⁻¹' R) := by
    rw [← e.image_symm_eq_preimage, ← hNpre]
    exact MMP.ProgramBaseChange.isExtremalRay_image e.symm hRay
  have hF : IsNegativeExtremalFace ℝ
      (relativeClosedConeOfCurves sX sX : Set (RelativeNumericalCurveClasses sX sX))
      ((MMP.Fourfold.QDivisor.curveForm sX D hD).comp
        (relativeToAbsolute sX sX)) (e ⁻¹' R) :=
    ⟨hFray.1, hFray.1.2.2.1, fun z hz hz0 =>
      hneg (e z) hz fun h => hz0 (e.injective (by rw [h, map_zero]))⟩
  have hclass : ∀ (A : ProperCurve sX) (hA : A.IsContractedBy sX),
      A.relativeClass sX hA ∈ e ⁻¹' R ↔ A.IsContractedBy f := by
    intro A hA
    rw [hf.isContractedBy_iff A]
    change e (A.relativeClass sX hA) ∈ R ↔ _
    rw [show e (A.relativeClass sX hA) = OneCycle.numericalClass sX (A.cycle ℝ) from
      isNaturalRelativeMap_relativeToAbsolute sX sX _]
  exact ⟨hF, hclass⟩

/-- **Descent of a Cartier divisor of degree zero on the contracted ray.** Let `(X, C)` be a
projective klt pair, `R` a `(K + C)`-negative extremal ray and `f : X ⟶ Z` its contraction, `f`
birational. A Cartier divisor `D` of degree zero on every curve contracted by `f` is, up to the
divisor of a rational function `u` of `Z`, the pull-back of a Cartier divisor `E` of `Z`. -/
private theorem exists_sub_pullback_eq_principalDivisor {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of k)} {K : Divisor X}
    {C : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hC : IsKltPair sX C) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + C) R)
    (hf : IsContractionOfRay sX sZ R f) (hfb : IsBirationalMorphism f)
    {D : Divisor X} (hDc : D.IsCartier)
    (hD0 : ∀ A : ProperCurve sX, A.IsContractedBy f → D.degreeOn k sX A.ι A.dim_le hDc = 0) :
    ∃ (E : Divisor Z) (hEc : E.IsCartier)
      (hfE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp)
      (u : (RationalFunctions Z)ˣ)
      (hu : ∀ W : irreducibleComponents X,
        f (componentGenericPoint X W) ∉ (principalDivisor u).supp),
      D - E.pullback (f := f) hEc hfE = principalDivisor (pullbackRationalFunction f u hu) := by
  have hP := hC.1
  have := hP.isAlgClosed
  have := hP.charZero
  obtain ⟨n, hKn⟩ := hK
  have hklt : MMP.Mori.IsKltPair sX n K C := (isKltPair_iff_mori_isKltPair sX hKn hP).mp hC
  have hC0 : 0 ≤ C := hP.nonneg
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  have hS : MMP.Mori.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
      ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance,
        inferInstance⟩, MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) := hS
  have hset : IsProjectiveSetting k sX (𝟙 (Spec (.of k))) sX :=
    ⟨‹_›, ‹_›, hX, hS, Category.comp_id sX⟩
  obtain ⟨hF, hclass⟩ :=
    isNegativeExtremalFace_preimage_relativeToAbsolute hklt.1.2.2 hR hf
  -- the contraction `ψ : X ⟶ Z₀` of `R` over the base point, and descent along it
  obtain ⟨Z₀, ψ, g, hψ⟩ := exists_isRelativeContractionOfFace_of_isNegativeExtremalFace hset hklt
    hC0 hF
  have := hDc.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨eL⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hklt hC0 hF hψ D.divisorialSheaf fun A hA hAR => hD0 A ((hclass A hA).mp hAR)
  -- `ψ` factors through `f`
  haveI : IsIntegral Z₀ := isIntegral_of_isIso_app ψ hψ.isIso_app
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hψ.isProjectiveMorphism
  haveI : AlgebraicGeometry.IsVariety k g := (MMP.Mori.isVariety_iff k g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : IsProper (ψ ≫ g) := by rw [hψ.comp_eq]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  haveI := AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety k sX
  have hψp : IsProjectiveMorphism ψ :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sX g ψ hψ.comp_eq
  obtain ⟨φ, hφ, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hψp hψ.comp_eq hR.2.1
    (fun A hA => (hψ.isContractedBy_iff A fun _ _ => Subsingleton.elim _ _).mpr
      ((hclass A _).mpr ((hf.isContractedBy_iff A).mpr hA))) hf
  haveI := hLZ
  have eψ : D.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback φ).obj LZ) :=
    eL ≪≫ (Scheme.Modules.pullbackCongr hφ.symm).app LZ ≪≫
      ((Scheme.Modules.pullbackComp f φ).app LZ).symm
  -- a Cartier divisor of `Z` and a rational function
  obtain ⟨E, hEc, ⟨e'⟩⟩ :=
    MMP.Mori.exists_isCartier_divisorialSheaf_iso ((Scheme.Modules.pullback φ).obj LZ)
  have := hfb.isDominant
  have hfE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f E
  obtain ⟨e''⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (f := f) hEc hfE
  obtain ⟨u, hu⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (eψ ≪≫ (Scheme.Modules.pullback f).mapIso e'.symm ≪≫ e''.symm)
  obtain ⟨uZ, huZ, rfl⟩ := exists_pullbackRationalFunction_eq hfb u
  exact ⟨E, hEc, hfE, uZ, huZ, hu⟩

/- ### Strict transforms across the step -/

section StrictTransform

variable {k : Type} [Field k] {X Z X' : Scheme.{0}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Every prime divisor `P` of `X⁺` lies over a prime divisor `Q` of `Z` which is the image of a
prime divisor `Pm` of `X`, and the coefficient of `P` in a strict transform from `X` is that of
`Pm`. -/
private theorem exists_primeDivisor_flipTransform_apply (hZ : IsNormalVariety k sZ) [IsProper f]
    (hfb : IsBirationalMorphism f) (hfp : IsSmallMorphism sX' sZ fp)
    (P : MMP.Mori.PrimeDivisor X') :
    ∃ (Pm : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Z),
      f Pm.genericPoint = Q.genericPoint ∧ fp P.genericPoint = Q.genericPoint ∧
        ∀ {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
          flipTransform f fp D P = D Pm := by
  haveI : IsProper fp := hfp.isProper
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI := hfb.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfb
    hfp P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  have := Q.isDiscreteValuationRing_localRing
  refine ⟨Pm, Q, hPmQ', hPQ', fun D => ?_⟩
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective fp.surjective
    hPmQ' hPQ' (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp
      hfp.isBirationalMorphism Q.coheight_genericPoint.le) D

/-- The strict transform of `f^* E + div(f^* u)` is `(f⁺)^* E + div((f⁺)^* u)`: each prime
divisor of `X⁺` and its strict transform on `X` lie over the same prime divisor of `Z`, with
isomorphic local rings. -/
private theorem flipTransform_add_principalDivisor (hZ : IsNormalVariety k sZ) [IsProper f]
    (hfb : IsBirationalMorphism f) (hfp : IsSmallMorphism sX' sZ fp) {E : Divisor Z}
    (hEc : E.IsCartier)
    {hE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp}
    {hE' : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ E.supp}
    {D₁ : Divisor X} {D₂ : Divisor X'} (h₁ : E.IsPullback f hE D₁) (h₂ : E.IsPullback fp hE' D₂)
    (u : (RationalFunctions Z)ˣ)
    (hu : ∀ W : irreducibleComponents X,
      f (componentGenericPoint X W) ∉ (principalDivisor u).supp)
    (hu' : ∀ W : irreducibleComponents X',
      fp (componentGenericPoint X' W) ∉ (principalDivisor u).supp) :
    flipTransform f fp (D₁ + principalDivisor (pullbackRationalFunction f u hu)) =
      D₂ + principalDivisor (pullbackRationalFunction fp u hu') := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨Pm, Q, hPm, hP, htr⟩ := exists_primeDivisor_flipTransform_apply hZ hfb hfp P
  have := isIso_stalkMap_of_map_eq_genericPoint hfb hPm
  have := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hP
  rw [htr]
  change DivisorWithCoeffs.coeff _ Pm = DivisorWithCoeffs.coeff _ P
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
    MMP.Positivity.coeff_eq_of_isPullback Pm Q hPm hEc h₁,
    MMP.Positivity.coeff_eq_of_isPullback P Q hP hEc h₂,
    MMP.Positivity.coeff_eq_of_isPullback Pm Q hPm (Divisor.isCartier_principalDivisor u)
      (Divisor.isPullback_principalDivisor u hu),
    MMP.Positivity.coeff_eq_of_isPullback P Q hP (Divisor.isCartier_principalDivisor u)
      (Divisor.isPullback_principalDivisor u hu')]

/-- The strict transform from `X` to `X⁺` undoes the strict transform from `X⁺` to `X`. -/
private theorem flipTransform_flipTransform (hZ : IsNormalVariety k sZ) [IsProper f]
    (hfb : IsBirationalMorphism f) (hfp : IsSmallMorphism sX' sZ fp) {R : Type*}
    [AddCommMonoid R] (D' : DivisorWithCoeffs R X') :
    flipTransform f fp (flipTransform fp f D') = D' := by
  haveI : IsProper fp := hfp.isProper
  haveI := hfb.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  refine Finsupp.ext fun P => ?_
  obtain ⟨Pm, Q, hPm, hP, htr⟩ := exists_primeDivisor_flipTransform_apply hZ hfb hfp P
  have := Q.isDiscreteValuationRing_localRing
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  rw [htr, flipTransform_apply_of_map_genericPoint
    hfp.isBirationalMorphism.functionFieldMap_bijective f.surjective hP hPm
    (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      Q.coheight_genericPoint.le)]

end StrictTransform

/- ### Numerical triviality across the step -/

/-- Adding a principal divisor does not change the degree on a proper curve. -/
private theorem degreeOn_add_principalDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] (C : ProperCurve sX) {D : Divisor X}
    (hD : D.IsCartier) (φ : (RationalFunctions X)ˣ) :
    (D + principalDivisor φ).degreeOn k sX C.ι C.dim_le
        (hD.add (Divisor.isCartier_principalDivisor φ)) =
      D.degreeOn k sX C.ι C.dim_le hD := by
  have hdc := Divisor.isCartier_principalDivisor φ
  rw [Divisor.degreeOn_add k sX C.ι C.dim_le D _ hD hdc]
  have hiso := (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
  have := hdc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor φ).degreeOn k sX C.ι C.dim_le hdc =
      (0 : Divisor X).degreeOn k sX C.ι C.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX C.ι C.dim_le hiso
  rw [h1, Divisor.degreeOn_zero' k sX C.ι C.dim_le, add_zero]

/-- Let `f : X ⟶ Z` be proper and surjective over `k` and `Dₗ = f^* Eₗ + div(f^* uₗ)`. If
`∑ₗ bₗ (Dₗ · A) = 0` on every curve `A` contracted by `f ≫ g`, then `∑ₗ bₗ (Eₗ · Γ) = 0` on every
curve `Γ` of `Z` contracted by `g`. -/
private theorem sum_mul_degreeOn_eq_zero_of_pullback {k : Type} [Field k] {X Z T : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sX] [LocallyOfFiniteType sX]
    [IsSeparated sZ] [LocallyOfFiniteType sZ] {f : X ⟶ Z} (hfZ : f ≫ sZ = sX) [IsProper f]
    [Surjective f] (g : Z ⟶ T) {n : ℕ} (b : Fin n → ℝ) {Dl : Fin n → Divisor X}
    (hDl : ∀ l, (Dl l).IsCartier) {E : Fin n → Divisor Z} (hEc : ∀ l, (E l).IsCartier)
    (hfE : ∀ l, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (E l).supp)
    (u : Fin n → (RationalFunctions Z)ˣ)
    (hu : ∀ l, ∀ W : irreducibleComponents X,
      f (componentGenericPoint X W) ∉ (principalDivisor (u l)).supp)
    (hDl_eq : ∀ l, Dl l = (E l).pullback (f := f) (hEc l) (hfE l) +
      principalDivisor (pullbackRationalFunction f (u l) (hu l)))
    (hsumA : ∀ A : ProperCurve sX, A.IsContractedBy (f ≫ g) →
      ∑ l, b l * ((Dl l).degreeOn k sX A.ι A.dim_le (hDl l) : ℝ) = 0)
    (Γ' : ProperCurve sZ) (hΓg : Γ'.IsContractedBy g) :
    ∑ l, b l * ((E l).degreeOn k sZ Γ'.ι Γ'.dim_le (hEc l) : ℝ) = 0 := by
  have h₁ := fun l => Divisor.isPullback_pullback (f := f) (hEc l) (hfE l)
  obtain ⟨A, hAΓ, hAim⟩ := exists_properCurve_map_eq_image_closure sX sZ f hfZ Γ'
  have hAc : A.IsContractedBy (f ≫ g) := by
    intro x hx
    have hfx : f x ∈ closure {Γ'.point} := hAim ▸ ⟨x, hx, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hΓg _ hfx, ← hAΓ]
  have hAnc : ¬ A.IsContractedBy f := by
    intro hA
    refine ProperCurve.closure_point_ne_singleton Γ' (Set.Subset.antisymm ?_ subset_closure)
    rw [← hAim]
    rintro _ ⟨x, hx, rfl⟩
    exact (hA x hx).trans hAΓ
  have hdegA : ∀ l, (Dl l).degreeOn k sX A.ι A.dim_le (hDl l) =
      (residueFieldDegree f A.point : ℤ) * (E l).degreeOn k sZ Γ'.ι Γ'.dim_le (hEc l) := by
    intro l
    rw [Divisor.degreeOn_congr (hDl_eq l) _ (((h₁ l).isCartier (hEc l)).add
      (Divisor.isCartier_principalDivisor _)),
      degreeOn_add_principalDivisor A ((h₁ l).isCartier (hEc l)) _,
      MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_mul f hfZ (hEc l) (h₁ l) A Γ' hAΓ.symm]
  have hS := hsumA A hAc
  simp only [hdegA, Int.cast_mul, Int.cast_natCast] at hS
  have hpos : (0 : ℝ) < residueFieldDegree f A.point := by
    exact_mod_cast MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy f hfZ A hAnc
  have : (residueFieldDegree f A.point : ℝ) *
      ∑ l, b l * ((E l).degreeOn k sZ Γ'.ι Γ'.dim_le (hEc l) : ℝ) = 0 := by
    rw [Finset.mul_sum, ← hS]
    exact Finset.sum_congr rfl fun l _ => by ring
  exact (mul_eq_zero.mp this).resolve_left hpos.ne'

/-- Let `f⁺ : X⁺ ⟶ Z` be over `k`. If `∑ₗ bₗ (Eₗ · Γ) = 0` on every curve `Γ` of `Z` contracted by
`g`, then `∑ₗ bₗ ((f⁺)^* Eₗ + div((f⁺)^* uₗ)) · C = 0` on every curve `C` of `X⁺` contracted by
`f⁺ ≫ g`. -/
private theorem sum_mul_degreeOn_pullback_add_principalDivisor_eq_zero {k : Type} [Field k]
    {X' Z T : Scheme.{0}}
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    {fp : X' ⟶ Z} [QuasiCompact (fp ≫ sZ)] (g : Z ⟶ T) {n : ℕ} (b : Fin n → ℝ)
    {E : Fin n → Divisor Z} (hEc : ∀ l, (E l).IsCartier)
    (hfpE : ∀ l, ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ (E l).supp)
    (u : Fin n → (RationalFunctions Z)ˣ)
    (hfpu : ∀ l, ∀ W : irreducibleComponents X',
      fp (componentGenericPoint X' W) ∉ (principalDivisor (u l)).supp)
    (hE : ∀ Γ : ProperCurve sZ, Γ.IsContractedBy g →
      ∑ l, b l * ((E l).degreeOn k sZ Γ.ι Γ.dim_le (hEc l) : ℝ) = 0)
    (C' : ProperCurve (fp ≫ sZ)) (hC' : C'.IsContractedBy (fp ≫ g)) :
    ∑ l, b l * (((E l).pullback (f := fp) (hEc l) (hfpE l) +
      principalDivisor (pullbackRationalFunction fp (u l) (hfpu l))).degreeOn k (fp ≫ sZ)
        C'.ι C'.dim_le
        (((Divisor.isPullback_pullback (f := fp) (hEc l) (hfpE l)).isCartier (hEc l)).add
          (Divisor.isCartier_principalDivisor _)) : ℝ) = 0 := by
  have h₂ := fun l => Divisor.isPullback_pullback (f := fp) (hEc l) (hfpE l)
  simp only [degreeOn_add_principalDivisor C' ((h₂ _).isCartier (hEc _))]
  by_cases hc : C'.IsContractedBy fp
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_zero fp rfl (hEc l) (h₂ l) C' hc]
    simp
  set Γ' : ProperCurve sZ := ⟨fp C'.point, MMP.Fourfold.Oai4C1.isProperCurve_map fp rfl C' hc⟩
  simp only [fun l => MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_mul fp rfl (hEc l) (h₂ l) C' Γ'
    rfl]
  have hS := hE Γ' (MMP.Fourfold.Oai4C1.isContractedBy_map fp rfl g C' hc hC')
  push_cast
  rw [← mul_zero (residueFieldDegree fp C'.point : ℝ), ← hS, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **Numerically trivial divisors transform to numerically trivial divisors.** Let
`f : X ⟶ Z ⟵ X⁺ : f⁺` with `f` proper, surjective and birational over `k`, `f⁺` small, and suppose
every Cartier divisor of degree zero on the curves contracted by `f` is, up to a principal
divisor pulled back from `Z`, a pull-back from `Z`. If `N` is numerically trivial over `g : Z ⟶ T`
(through `f`), then its strict transform is numerically trivial over `g` (through `f⁺`). -/
private theorem isNumericallyTrivialOver_flipTransform {k : Type} [Field k]
    {X Z X' T : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sX]
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hfZ : f ≫ sZ = sX) [IsProper f] (hfs : Function.Surjective f)
    (hZ : IsNormalVariety k sZ) [IsProper sZ] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism (fp ≫ sZ) sZ fp)
    (hdesc : ∀ (D : Divisor X) (hDc : D.IsCartier),
      (∀ A : ProperCurve sX, A.IsContractedBy f → D.degreeOn k sX A.ι A.dim_le hDc = 0) →
      ∃ (E : Divisor Z) (hEc : E.IsCartier)
        (hfE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp)
        (u : (RationalFunctions Z)ˣ)
        (hu : ∀ W : irreducibleComponents X,
          f (componentGenericPoint X W) ∉ (principalDivisor u).supp),
        D - E.pullback (f := f) hEc hfE = principalDivisor (pullbackRationalFunction f u hu))
    (g : Z ⟶ T) {N : RDivisor X} (hN : IsNumericallyTrivialOver k sX (f ≫ g) N) :
    IsNumericallyTrivialOver k (fp ≫ sZ) (fp ≫ g) (flipTransform f fp N) := by
  have := hfb.isDominant
  have := hfp.isBirationalMorphism.isDominant
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hfZ ▸ inferInstance
  haveI : Surjective f := ⟨hfs⟩
  obtain ⟨hNc, hN0⟩ := isNumericallyTrivialOver_iff.mp hN
  obtain ⟨n, b, Dl, hDl, rfl, hind⟩ := exists_eq_sum_toRDivisor_of_intIndependent hNc
  have hsumA : ∀ A : ProperCurve sX, A.IsContractedBy (f ≫ g) →
      ∑ l, b l * ((Dl l).degreeOn k sX A.ι A.dim_le (hDl l) : ℝ) = 0 := fun A hA =>
    hN0 A hA _ _ _ _ (MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX A b Dl hDl)
  have hdeg0 : ∀ l (A : ProperCurve sX), A.IsContractedBy f →
      (Dl l).degreeOn k sX A.ι A.dim_le (hDl l) = 0 := by
    intro l A hA
    have hA' : A.IsContractedBy (f ≫ g) := fun x hx => by
      simp only [Scheme.Hom.comp_apply, hA x hx]
    refine hind (fun l => (Dl l).degreeOn k sX A.ι A.dim_le (hDl l)) ?_ l
    simpa only [mul_comm] using hsumA A hA'
  choose E hEc hfE u hu hDE using fun l => hdesc (Dl l) (hDl l) (hdeg0 l)
  have hfpE := fun l =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp (E l)
  have hfpu := fun l =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp
      (principalDivisor (u l))
  have h₂ := fun l => Divisor.isPullback_pullback (f := fp) (hEc l) (hfpE l)
  have hDl_eq : ∀ l, Dl l = (E l).pullback (f := f) (hEc l) (hfE l) +
      principalDivisor (pullbackRationalFunction f (u l) (hu l)) := fun l => by
    rw [← hDE l, add_sub_cancel]
  have hTc : ∀ l, ((E l).pullback (f := fp) (hEc l) (hfpE l) +
      principalDivisor (pullbackRationalFunction fp (u l) (hfpu l))).IsCartier := fun l =>
    ((h₂ l).isCartier (hEc l)).add (Divisor.isCartier_principalDivisor _)
  have hTN : flipTransform f fp (∑ l, b l • Divisor.toRDivisor (Dl l)) = ∑ l, b l •
      Divisor.toRDivisor ((E l).pullback (f := fp) (hEc l) (hfpE l) +
        principalDivisor (pullbackRationalFunction fp (u l) (hfpu l))) := by
    rw [flipTransform_sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← toRDivisor_flipTransform, hDl_eq l, flipTransform_add_principalDivisor hZ hfb hfp
      (hEc l) (Divisor.isPullback_pullback (hEc l) (hfE l)) (h₂ l) (u l) (hu l) (hfpu l)]
  refine isNumericallyTrivialOver_iff.mpr ⟨⟨n, b, _, hTc, by
    rw [hTN]
    simp only [toRDivisor_eq_mapCoeffs]⟩, fun C' hC' m' r' L' x hx => ?_⟩
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber k (fp ≫ sZ) C' b _ hTc hTN hx]
  exact sum_mul_degreeOn_pullback_add_principalDivisor_eq_zero g b hEc hfpE u hfpu
    (sum_mul_degreeOn_eq_zero_of_pullback hfZ g b hDl hEc hfE u hu hDl_eq hsumA) C' hC'

/-- An isomorphism onto a normal variety is a small morphism. -/
private theorem isSmallMorphism_of_isIso {k : Type} [Field k] {X' Z : Scheme.{0}}
    [IsIntegral X'] [IsNormal X'] {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ)
    (fp : X' ⟶ Z) [IsIso fp] : IsSmallMorphism (fp ≫ sZ) sZ fp := by
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : MMP.Mori.IsVariety k (fp ≫ sZ) := (MMP.Mori.isVariety_iff k _).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hV : (⊤ : Z.Opens) ≤ biregularLocus fp :=
    le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance)
  exact
    { isNormalVariety_source := ⟨this, inferInstance⟩
      isNormalVariety_target := hZ
      comp_eq := rfl
      isProper := inferInstance
      isBirationalMorphism := isBirationalMorphism_of_isIso fp
      two_le_codimension := le_closedsCodimension_iff.mpr fun W hW => by
        obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
        exact absurd (hV (Set.mem_univ (fp x))) (hW hx) }

/-- A transform which is onto on `ℝ`-Cartier divisors of a `ℚ`-factorial `X⁺` and preserves
numerical triviality carries a numerically spanning family to one, using only the indices whose
transform is nonzero. -/
private theorem exists_isNumericallyEquivalentOver_sum_flipTransform {k : Type} [Field k]
    {X Z X' : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {sX' : X' ⟶ Spec (.of k)}
    [QuasiCompact sX'] {f : X ⟶ Z} {fp : X' ⟶ Z} (hX'Q : IsQFactorial sX')
    (h2 : ∀ N : RDivisor X, IsNumericallyTrivialOver k sX sX N →
      IsNumericallyTrivialOver k sX' sX' (flipTransform f fp N))
    (h4 : ∀ D' : RDivisor X', IsCartierCombination D' →
      ∃ D : RDivisor X, IsCartierCombination D ∧ flipTransform f fp D = D')
    {n : ℕ} (D : Fin n → RDivisor X)
    (hspan : ∀ E : RDivisor X, IsCartierCombination E →
      ∃ a : Fin n → ℝ, IsNumericallyEquivalentOver k sX sX E (∑ i, a i • D i))
    (E' : RDivisor X') :
    ∃ a : Fin n → ℝ, (∀ i, flipTransform f fp (D i) = 0 → a i = 0) ∧
      IsNumericallyEquivalentOver k sX' sX' E' (∑ i, a i • flipTransform f fp (D i)) := by
  obtain ⟨E, hE, rfl⟩ := h4 E' (isCartierCombination_of_isQFactorial hX'Q _)
  obtain ⟨a, ha⟩ := hspan E hE
  have htr := h2 _ (isNumericallyTrivialOver_sub ha)
  rw [map_sub, flipTransform_sum_smul] at htr
  classical
  refine ⟨fun i => if flipTransform f fp (D i) = 0 then 0 else a i, fun i hi => if_pos hi, ?_⟩
  have hsum : ∑ i, (if flipTransform f fp (D i) = 0 then 0 else a i) • flipTransform f fp (D i) =
      ∑ i, a i • flipTransform f fp (D i) :=
    Finset.sum_congr rfl fun i _ => by split_ifs with h0 <;> simp [h0]
  rw [hsum]
  exact isNumericallyEquivalentOver_of_sub (isCartierCombination_of_isQFactorial hX'Q _)
    (isCartierCombination_of_isQFactorial hX'Q _) htr

/-- **Numerical classes along an elementary klt step.** Let `(X, C)` be a projective
`ℚ`-factorial klt pair with canonical divisor `K`, `R` a `(K + C)`-negative extremal ray of
`NE̅(X)` with contraction `f : X ⟶ Z`, and `f⁺ : X⁺ ⟶ Z` with `X⁺` projective and `ℚ`-factorial,
such that either `f` is divisorial and `f⁺` is an isomorphism, or `f⁺` is a flip of `f`. Let
`h : Z ⟶ S` place the step over a projective variety `S`. Then the transform
`T = flipTransform f f⁺` satisfies:

* `T` sends `ℝ`-Cartier divisors to `ℝ`-Cartier divisors;
* `T` sends numerically trivial divisors to numerically trivial divisors;
* `T` sends divisors numerically trivial over `S` to divisors numerically trivial over `S`;
* every `ℝ`-Cartier divisor on `X⁺` is `T D` for some `ℝ`-Cartier divisor `D` on `X`;
* if `D₁, …, Dₙ` are `ℝ`-Cartier and span `N¹(X)_ℝ`, the `T Dᵢ` span `N¹(X⁺)_ℝ`, using only
  the indices with `T Dᵢ ≠ 0`. -/
@[mmp "lem_fourfold_numerical_classes_transport"]
public theorem IsKltPair.isNumericallyTrivialOver_flipTransform_of_isContractionOfRay
    {k : Type} [Field k] {X Z X' S : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sS : S ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {K : Divisor X} {C : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    {fp : X' ⟶ Z} {h : Z ⟶ S}
    (hC : IsKltPair sX C) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hXQ : IsQFactorial sX)
    (hX' : MMP.Mori.IsProjectiveVariety k sX') (hX'Q : IsQFactorial sX')
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + C) R)
    (hf : IsContractionOfRay sX sZ R f)
    (hstep : (IsBirationalMorphism f ∧
        (∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
          IsIso fp) ∨
      ∃ D : QDivisor X, IsFlipOf sX sZ sX' D f fp)
    (hS : MMP.Mori.IsProjectiveVariety k sS) (hh : h ≫ sS = sZ) :
    (∀ D : RDivisor X, IsCartierCombination D → IsCartierCombination (flipTransform f fp D)) ∧
      (∀ N : RDivisor X, IsNumericallyTrivialOver k sX sX N →
        IsNumericallyTrivialOver k sX' sX' (flipTransform f fp N)) ∧
      (∀ N : RDivisor X, IsNumericallyTrivialOver k sX (f ≫ h) N →
        IsNumericallyTrivialOver k sX' (fp ≫ h) (flipTransform f fp N)) ∧
      (∀ D' : RDivisor X', IsCartierCombination D' →
        ∃ D : RDivisor X, IsCartierCombination D ∧ flipTransform f fp D = D') ∧
      ∀ (n : ℕ) (D : Fin n → RDivisor X), (∀ i, IsCartierCombination (D i)) →
        (∀ E : RDivisor X, IsCartierCombination E →
          ∃ a : Fin n → ℝ, IsNumericallyEquivalentOver k sX sX E (∑ i, a i • D i)) →
        ∀ E' : RDivisor X', IsCartierCombination E' →
          ∃ a : Fin n → ℝ, (∀ i, flipTransform f fp (D i) = 0 → a i = 0) ∧
            IsNumericallyEquivalentOver k sX' sX' E' (∑ i, a i • flipTransform f fp (D i)) := by
  have hfC := hf.toIsContraction
  have hZv := hfC.isNormalVariety_target
  have : IsIntegral Z := hZv.1.toIsIntegral
  have : IsNormal Z := hZv.2
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : QuasiCompact sZ := hZv.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsIntegral X' := hX'.toIsVariety.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  have : IsProper f := isProper_of_isProjectiveMorphism _ hfC.isProjectiveMorphism
  have : IsProper sZ := by
    have : Surjective f := ⟨hfC.surjective⟩
    have : UniversallyClosed (f ≫ sZ) := by rw [hf.comp_eq]; infer_instance
    have := UniversallyClosed.of_comp_surjective f sZ
    have : IsSeparated sZ := hZv.1.toIsSeparated
    constructor
  have hfb : IsBirationalMorphism f := by
    rcases hstep with h | ⟨D, hD⟩
    · exact h.1
    · exact hD.isSmallMorphism.isBirationalMorphism
  have hsmall : IsSmallMorphism (fp ≫ sZ) sZ fp := by
    rcases hstep with ⟨-, -, hiso⟩ | ⟨D, hD⟩
    · exact isSmallMorphism_of_isIso hZv fp
    · have h := hD.isSmallMorphism_flip
      rwa [← h.comp_eq] at h
  have hkey := fun {T : Scheme.{0}} (g : Z ⟶ T) {N : RDivisor X} hN =>
    isNumericallyTrivialOver_flipTransform hf.comp_eq hfC.surjective hZv hfb hsmall
      (fun D hDc hD0 => exists_sub_pullback_eq_principalDivisor hC hK hX hR hf hfb hDc hD0) g
      (N := N) hN
  have htwist : ∀ {T : Scheme.{0}} (g : X' ⟶ T) (N₁ N₂ : RDivisor X'),
      IsNumericallyEquivalentOver k (fp ≫ sZ) g N₁ N₂ →
        IsNumericallyEquivalentOver k sX' g N₁ N₂ := by
    rcases hstep with ⟨-, -, hiso⟩ | ⟨D, hD⟩
    · have := hC.1.isAlgClosed
      haveI : IsProper sX' := isProper_of_isProjectiveMorphism _ hX'.isProjective
      exact fun _ _ _ _ hN => isNumericallyEquivalentOver_of_isAlgClosed hN
    · intro T g N₁ N₂ hN
      obtain rfl := hD.isSmallMorphism_flip.comp_eq
      exact hN
  have h2 : ∀ N : RDivisor X, IsNumericallyTrivialOver k sX sX N →
      IsNumericallyTrivialOver k sX' sX' (flipTransform f fp N) := by
    intro N hN
    have hN' : IsNumericallyTrivialOver k sX (f ≫ sZ) N := by rwa [hf.comp_eq]
    have h := hkey sZ hN'
    exact htwist _ _ _ ⟨h.1, h.2.1, fun C _ => h.2.2 C fun _ _ => Subsingleton.elim _ _⟩
  have h4 : ∀ D' : RDivisor X', IsCartierCombination D' →
      ∃ D : RDivisor X, IsCartierCombination D ∧ flipTransform f fp D = D' := fun D' _ =>
    ⟨flipTransform fp f D', isCartierCombination_of_isQFactorial hXQ _,
      flipTransform_flipTransform hZv hfb hsmall D'⟩
  exact ⟨fun D _ => isCartierCombination_of_isQFactorial hX'Q _, h2,
    fun N hN => htwist _ _ _ (hkey h hN), h4, fun n D _ hspan E' _ =>
      exists_isNumericallyEquivalentOver_sum_flipTransform hX'Q h2 h4 D hspan E'⟩

end MMP.Fourfold
