module
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import MMP.AlgebraicGeometry.Bertini.FreeSystemIrreducible
public import MMP.AlgebraicGeometry.ProjectiveSpace.GeneralLinearSections
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeNonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# General hyperplane sections of a morphism to projective space

Let `k` be an algebraically closed field of characteristic zero, `V` a variety over `k`,
`φ : V ⟶ ℙᴷ_k` a morphism over `k` and `Z_l` (`l ∈ ι`, `ι` finite) irreducible closed subsets of
`V`. For the hyperplane `H = V(∑ᵢ aᵢ Tᵢ)` with `[a]` in a dense open of the dual projective space
`(ℙᴷ_k)^∨`:

1. if `V` is smooth over `k`, so is `φ⁻¹(H)` (possibly empty);
2. if `dim closure (φ(V)) ≥ 2`, then `φ⁻¹(H)` is irreducible;
3. no `Z_l` lies in `φ⁻¹(H)`; if `φ(Z_l)` is a point, `Z_l ∩ φ⁻¹(H) = ∅`, and otherwise every
   irreducible component of `Z_l ∩ φ⁻¹(H)` has dimension `dim Z_l - 1`, and `Z_l ∩ φ⁻¹(H)` is
   nonempty when `Z_l` is moreover proper over `k`.

Moreover, for finitely many constructible `W_u ⊆ ℙᴷ_k` and `c : ℕ`, for general
`(H_1, …, H_c)` the set `W_u ∩ H_1 ∩ ⋯ ∩ H_c` is empty if `c > dim W_u` and nonempty of dimension
`dim W_u - c` if `c ≤ dim W_u`.

## Main definitions

* `MMP.Threefold.Bridges.twistOne`: the twisting sheaf `𝒪(1)` on `ℙᴷ_k`, and
  `MMP.Threefold.Bridges.formSection` the global section of a linear form.
* `MMP.Threefold.Bridges.pulledSystem`: the system `φ^*T₀, …, φ^*T_K` of sections of
  `MMP.Threefold.Bridges.pullTwist φ = φ^*𝒪(1)`.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_hyperplaneSection`: the statement above.
* `MMP.Threefold.Bridges.zeroScheme_pulledSystem`: the member of `pulledSystem φ` with
  coefficients `a` cuts out `hyperplaneSection φ a`.
* `MMP.Threefold.Bridges.iSup_nonvanishingOpen_pulledSystem`: `pulledSystem φ` generates
  `φ^*𝒪(1)`.
* `MMP.Threefold.Bridges.exists_dense_open_of_polynomial`: a nonzero polynomial in the
  coefficients of a linear form is nonzero at some rescaling of every point of a dense open of
  the dual projective space.
* `MMP.Threefold.Bridges.hyperplaneSection_smul`,
  `MMP.Threefold.Bridges.support_hyperplane_linearForm_smul`: a nonzero rescaling of the
  coefficient vector changes neither the hyperplane nor `φ⁻¹(H)`.
* `MMP.Threefold.Bridges.exists_polynomial_inter_hyperplanes`: the dimension count for general
  linear sections of finitely many constructible subsets of `ℙᴷ_k`.
* `MMP.Threefold.Bridges.hyperplaneSection_inter_of_image_inter_hyperplane`: a hyperplane
  cutting `φ(Z)` properly pulls back to a divisor cutting `Z` properly.
* `MMP.Threefold.Bridges.topologicalKrullDim_image_of_isEmbedding`: an embedding preserves the
  dimension of a subset.

## Implementation notes

`ℙᴷ_k` and its dual are both
`AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)`; the hyperplane
of a nonzero coefficient vector `a` is the point `MMP.Threefold.Bridges.dualPoint a` of the dual,
and `φ⁻¹(H)` is the closed subscheme `MMP.Threefold.Bridges.hyperplaneSection φ a`. A closed
subset `Z` is proper over `k` when its reduced closed subscheme is. An irreducible component of a
subset `A` is a maximal irreducible subset of `A`, and `dim T = dim Z - 1` is written
`dim T + 1 = dim Z`.

For the simultaneous cut by `c` hyperplanes, "a dense open of `((ℙᴷ_k)^∨)^c`" is given by the
nonvanishing of a nonzero polynomial `P` in the `c (K + 1)` coefficients of the linear forms. As
`k` is algebraically closed, the `k`-points of a dense open of the product contain the
nonvanishing locus of a nonzero multihomogeneous polynomial, and conversely the conclusion is
invariant under rescaling each form, so a nonzero `P` may be replaced by a nonzero
multihomogeneous component; the two formulations agree.

The smoothness and irreducibility come from the Bertini theorems for the free system
`φ^*T₀, …, φ^*T_K` of sections of `φ^*𝒪(1)`, whose general member is `φ⁻¹(H)`. The morphism to
`ℙᴷ` that this system defines lands in `𝐏(kᴷ⁺¹)`; it agrees with `φ`, read through the
identification of `ℙᴷ_k` with `𝐏(kᴷ⁺¹)`, at every closed point, which is all the comparison of
the dimensions of their images needs, since the image of a morphism from an irreducible scheme has
the dimension of its closure. The behaviour on the `Z_l` comes from the dimension count for general
hyperplane sections of the constructible sets `φ(Z_l)`, together with the codimension of an
effective Cartier divisor on the reduced closed subscheme supported on `Z_l`.

## References

* [O. Fujino et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
  (globalSectionsModule baseRingHom morphismOfGeneratingSections
    morphismOfGeneratingSections_base_eq)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec)

universe u

namespace MMP.Threefold.Bridges

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An irreducible subset of a `T₀` space with two distinct points has dimension at least one:
the closure of one of them is a proper irreducible closed subset. -/
private theorem one_le_topologicalKrullDim_of_isIrreducible {X : Type*} [TopologicalSpace X]
    [T0Space X] {W : Set X} (hW : IsIrreducible W) (hns : ¬ W.Subsingleton) :
    1 ≤ topologicalKrullDim W := by
  haveI : IrreducibleSpace W := Subtype.irreducibleSpace hW
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.mp hns
  have key : ∀ p ∈ W, ∀ q ∈ W, q ∉ closure ({p} : Set X) → 1 ≤ topologicalKrullDim W := by
    intro p hp q hq hqp
    unfold topologicalKrullDim
    refine Order.one_le_krullDim_iff.mpr
      ⟨⟨closure {(⟨p, hp⟩ : W)}, isIrreducible_singleton.closure, isClosed_closure⟩,
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) fun h => ?_
    have hmem : (⟨q, hq⟩ : W) ∈ closure {(⟨p, hp⟩ : W)} := by
      have : (closure {(⟨p, hp⟩ : W)} : Set W) = Set.univ :=
        congrArg (fun A : IrreducibleCloseds W => (A : Set W)) h
      rw [this]
      trivial
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Set.image_singleton] at hmem
    exact hqp hmem
  by_cases h1 : q ∈ closure ({p} : Set X)
  · by_cases h2 : p ∈ closure ({q} : Set X)
    · exact absurd (((specializes_iff_mem_closure.mpr h1).antisymm
        (specializes_iff_mem_closure.mpr h2)).eq) hpq
    · exact key q hq p hp h2
  · exact key p hp q hq h1

/-- A subsingleton has dimension less than one. -/
private theorem topologicalKrullDim_lt_one_of_subsingleton {X : Type*} [TopologicalSpace X]
    {W : Set X} (h : W.Subsingleton) : topologicalKrullDim W < 1 := by
  haveI : Subsingleton W := h.coe_sort
  exact (topologicalKrullDim_zero_of_discreteTopology W).trans_lt (by norm_num)

/-- A finite positive dimension is not its own successor. -/
private theorem add_one_ne_self {x : WithBot ℕ∞} {K : ℕ} (hx : x ≤ K) (h1 : 1 ≤ x) : x + 1 ≠ x := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((K : ℕ∞) : WithBot ℕ∞) := hx
      rw [WithBot.coe_le_coe] at this
      exact absurd this (by simp)
    | coe n =>
      intro h
      have : ((n + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (by exact_mod_cast this : n + 1 = n) (by omega)

variable {k : Type u} [Field k] {K : ℕ}

attribute [local instance] globalSectionsModule

/-- The twisting sheaf `𝒪(1)` on `ℙᴷ_k`. -/
noncomputable abbrev twistOne (k : Type u) [Field k] (K : ℕ) :
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Modules :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule
    (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k) ((1 : ℕ) : ℤ)

/-- `𝒪(1)` is invertible on `ℙᴷ_k`. -/
instance isInvertibleModule_twistOne : Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))
    (twistOne k K) :=
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.isInvertibleModule_twistingSheafOne _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (K + 1)) k)

/-- The global section of `𝒪(1)` of a linear form. -/
noncomputable abbrev formSection (l : MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1) :
    Γ(twistOne k K, ⊤) :=
  ProjectiveSpectrum.Proj.degreeSection (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k) 1 l

/-- A linear form does not vanish at a point of `ℙᴷ_k` exactly when it is outside its prime. -/
theorem mem_nonvanishingOpen_formSection_iff
    (l : MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1) (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :
    x ∈ nonvanishingOpen (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) (twistOne k K) (formSection l) ↔
      (l : MvPolynomial (Fin (K + 1)) k) ∉ x.asHomogeneousIdeal := by
  have h1 :=
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k)
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (K + 1)) k) (d := 1) one_pos 1 l
  change x ∈ Stacks.Ample.nonvanishingLocus (twistOne k K) (formSection l) ↔ _
  rw [show Stacks.Ample.nonvanishingLocus (twistOne k K) (formSection l) = _ from h1]
  exact Iff.rfl

/-- A point of `ℙᴷ_k` lies on the hyperplane of a linear form exactly when the form lies in its
homogeneous prime. -/
private theorem mem_support_hyperplane_iff
    (l : MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1) (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :
    x ∈ ((Stacks.ProjectiveSpace.hyperplane l).support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) ↔
      (l : MvPolynomial (Fin (K + 1)) k) ∈ x.asHomogeneousIdeal := by
  rw [← not_iff_not]
  exact (mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme _ (formSection l) x).symm.trans
    (mem_nonvanishingOpen_formSection_iff l x)

/-- The linear form of a coefficient vector, as a polynomial. -/
theorem coe_linearForm (a : Fin (K + 1) → k) :
    (linearForm a : MvPolynomial (Fin (K + 1)) k) = ∑ i, a i • MvPolynomial.X i := by
  simp [linearForm]

/-- The hyperplane of a coefficient vector does not change under a nonzero rescaling. -/
theorem support_hyperplane_linearForm_smul (a : Fin (K + 1) → k) {t : k} (ht : t ≠ 0) :
    ((Stacks.ProjectiveSpace.hyperplane (linearForm (t • a))).support :
        Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) =
      (Stacks.ProjectiveSpace.hyperplane (linearForm a)).support := by
  ext x
  rw [mem_support_hyperplane_iff, mem_support_hyperplane_iff]
  have h : (linearForm (t • a) : MvPolynomial (Fin (K + 1)) k) =
      MvPolynomial.C t * (linearForm a : MvPolynomial (Fin (K + 1)) k) := by
    rw [coe_linearForm, coe_linearForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [MvPolynomial.smul_eq_C_mul, mul_assoc]
  rw [h]
  exact Ideal.unit_mul_mem_iff_mem _ ((isUnit_iff_ne_zero.mpr ht).map MvPolynomial.C)

/-- **A nonzero polynomial in one linear form defines a dense open of the dual projective space**
on which some rescaling of the form is a nonzero of the polynomial. -/
theorem exists_dense_open_of_polynomial [Infinite k]
    {P : MvPolynomial (Fin 1 × Fin (K + 1)) k} (hP : P ≠ 0) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) ∧
      ∀ (a : Fin (K + 1) → k) (ha : a ≠ 0), dualPoint a ha ∈ U →
        ∃ t : k, t ≠ 0 ∧ MvPolynomial.eval (fun p => (fun _ : Fin 1 => t • a) p.1 p.2) P ≠ 0 := by
  classical
  set Q := MvPolynomial.rename (Prod.snd : Fin 1 × Fin (K + 1) → Fin (K + 1)) P
  have hQ0 : Q ≠ 0 := by
    refine fun h => hP (MvPolynomial.rename_injective _ ?_ (h.trans (map_zero _).symm))
    rintro ⟨i, j⟩ ⟨i', j'⟩ (h : j = j')
    rw [Subsingleton.elim i i', h]
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
    by_contra! h
    exact hQ0 ((MvPolynomial.sum_homogeneousComponent Q).symm.trans
      (Finset.sum_eq_zero fun i _ => h i))
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun a ha hmem => ?_⟩
  have hha : MvPolynomial.eval a (MvPolynomial.homogeneousComponent d Q) ≠ 0 := by
    intro h0
    change MvPolynomial.homogeneousComponent d Q ∉
      (RingHom.ker (MvPolynomial.eval a)).homogeneousCore
        (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k) at hmem
    exact hmem <| Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d Q⟩ ((RingHom.mem_ker).mpr h0)
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q a hha
  exact ⟨t, ht, by rwa [MvPolynomial.eval_rename] at htQ⟩

/-- The section of a linear form is `k`-linear in the form, for the `k`-structure of `ℙᴷ_k` given
by its structure morphism. -/
private theorem formSection_smul (r : k) (l : MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1) :
    letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
      ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
    r • formSection l = formSection (r • l) := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
    ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
  have hb : baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) r =
      Stacks.ProjectiveSpace.Cohomology.coeffScalar k K r := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Stacks.ProjectiveCohomology.projModelToSpec k K).appTop).hom r =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k K).appTop).hom r
    rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]
  change baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) r • formSection l = _
  rw [hb]
  exact Stacks.ProjectiveSpace.Cohomology.degreeSection_smul k K 1 r l

/-- `φ⁻¹(H)` does not change under a nonzero rescaling of the coefficient vector of `H`. -/
theorem hyperplaneSection_smul {V : Scheme.{u}} (φ : V ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))
    (a : Fin (K + 1) → k) {t : k} (ht : t ≠ 0) :
    hyperplaneSection φ (t • a) = hyperplaneSection φ a := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
    ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
  haveI : SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).sheaf.obj
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).ringCatSheaf.property (twistOne k K) :=
    (inferInstance : Stacks.Ample.IsInvertibleModule _ (twistOne k K))
  have hl : linearForm (t • a) = t • linearForm a :=
    Subtype.ext (by simp [coe_linearForm, Finset.smul_sum, smul_smul])
  have hs : formSection (linearForm (t • a)) =
      baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) t • formSection (linearForm a) := by
    rw [hl]
    exact (formSection_smul t _).symm
  change (zeroScheme _ (twistOne k K) (formSection (linearForm (t • a)))).comap φ =
    (zeroScheme _ (twistOne k K) (formSection (linearForm a))).comap φ
  rw [hs]
  exact congrArg (·.comap φ) (Stacks.Divisors.zeroScheme_smul_of_isUnit (twistOne k K) _
    ((isUnit_iff_ne_zero.mpr ht).map (baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))))

/-- The section of a linear form is additive in the form. -/
private theorem formSection_add (l l' : MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1) :
    formSection (l + l') = formSection l + formSection l' :=
  Stacks.ProjectiveSpace.Cohomology.degreeSection_add k K 1 l l'

/-- The section of `𝒪(1)` of a linear form, as a `k`-linear map. -/
private noncomputable def formSectionₗ :
    letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
      ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
    MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1 →ₗ[k] Γ(twistOne k K, ⊤) :=
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
    ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
  { toFun := formSection
    map_add' := formSection_add
    map_smul' := fun r l => (formSection_smul r l).symm }

/-- The section of `∑ᵢ aᵢ Tᵢ` is `∑ᵢ aᵢ` times the section of `Tᵢ`. -/
private theorem formSection_linearForm (a : Fin (K + 1) → k) :
    letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
      ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
    formSection (linearForm a) =
      ∑ i, a i • formSection ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩ := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
    ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
  have h := map_sum (formSectionₗ (k := k) (K := K))
    (fun i => a i • (⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩ :
      MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k 1)) Finset.univ
  simp only [map_smul] at h
  exact h

/-- A basis of `M` indexed by `Fin (K + 1)` identifies `ℙᴷ_k` with `𝐏(M)` as spaces. -/
private noncomputable def projHomeomorph {M : Type u} [AddCommGroup M] [Module k M]
    (b : Module.Basis (Fin (K + 1)) k M) :
    AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K) ≃ₜ projectiveSpaceOfModule k M where
  toFun := ProjectiveSpectrum.comap (SymPow.gradedMvPolynomialHom b)
    (irrelevant_le_map_gradedMvPolynomialHom b)
  invFun := ProjectiveSpectrum.comap (SymPow.gradedMvPolynomialInv b)
    (irrelevant_le_map_gradedMvPolynomialInv b)
  left_inv x := by
    refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun y => ?_))
    change (SymPow.gradedMvPolynomialHom b) ((SymPow.gradedMvPolynomialInv b) y) ∈
      x.asHomogeneousIdeal ↔ y ∈ x.asHomogeneousIdeal
    rw [SymPow.gradedMvPolynomialHom_apply]
    erw [AlgEquiv.apply_symm_apply]
  right_inv x := by
    refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun y => ?_))
    change (SymPow.gradedMvPolynomialInv b) ((SymPow.gradedMvPolynomialHom b) y) ∈
      x.asHomogeneousIdeal ↔ y ∈ x.asHomogeneousIdeal
    rw [SymPow.gradedMvPolynomialHom_apply]
    erw [AlgEquiv.symm_apply_apply]
  continuous_toFun := (ProjectiveSpectrum.comap _ _).continuous
  continuous_invFun := (ProjectiveSpectrum.comap _ _).continuous

/-- A basis carries a vector to the linear form of its coordinates. -/
private theorem equivMvPolynomial_ι {M : Type u} [AddCommGroup M] [Module k M]
    (b : Module.Basis (Fin (K + 1)) k M) (v : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k M v) =
      (linearForm (b.repr v) : MvPolynomial (Fin (K + 1)) k) := by
  rw [coe_linearForm]
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply]

/-- A degree-one element lies in the image point exactly when the linear form of its
coordinates lies in the original point. -/
private theorem ι_mem_projHomeomorph_iff {M : Type u} [AddCommGroup M] [Module k M]
    (b : Module.Basis (Fin (K + 1)) k M) (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) (v : M) :
    SymmetricAlgebra.ι k M v ∈ (projHomeomorph b x).asHomogeneousIdeal ↔
      (linearForm (b.repr v) : MvPolynomial (Fin (K + 1)) k) ∈ x.asHomogeneousIdeal := by
  rw [← equivMvPolynomial_ι]
  exact Iff.rfl

/-- A homeomorphism preserves constructibility. -/
private theorem isConstructible_image_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {S : Set X} (hS : Topology.IsConstructible S) :
    Topology.IsConstructible (e '' S) := by
  rw [e.image_eq_preimage_symm]
  exact hS.preimage_of_isOpenEmbedding e.symm.isOpenEmbedding

/-- An embedding preserves the dimension of a subset. -/
theorem topologicalKrullDim_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) (S : Set X) :
    topologicalKrullDim (f '' S) = topologicalKrullDim S := by
  have h := (hf.comp (Topology.IsEmbedding.subtypeVal (p := (· ∈ S)))).toHomeomorph
  have hr : Set.range (f ∘ Subtype.val : S → Y) = f '' S := by
    rw [Set.range_comp, Subtype.range_coe]
  have h2 := h.isHomeomorph.topologicalKrullDim_eq _
  rw [hr] at h2
  exact h2.symm

/-- In a space where `η` lies in every nonempty open set, a constructible set containing `η`
contains an open neighbourhood of `η`, and one missing `η` misses an open neighbourhood. -/
private theorem exists_isOpen_of_isConstructible {X : Type*} [TopologicalSpace X] {η : X}
    (hη : ∀ U : Set X, IsOpen U → U.Nonempty → η ∈ U) {s : Set X}
    (hs : Topology.IsConstructible s) :
    (η ∈ s → ∃ U, IsOpen U ∧ η ∈ U ∧ U ⊆ s) ∧ (η ∉ s → ∃ U, IsOpen U ∧ η ∈ U ∧ U ⊆ sᶜ) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun h => ⟨U, hU, h, le_rfl⟩, fun h => ⟨Set.univ, isOpen_univ, trivial, ?_⟩⟩
    intro x _ hx
    exact h (hη U hU ⟨x, hx⟩)
  | union s _ t _ hs ht =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · obtain ⟨U, hU, hηU, hUs⟩ := hs.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_left⟩
      · obtain ⟨U, hU, hηU, hUs⟩ := ht.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_right⟩
    · rw [Set.mem_union, not_or] at h
      obtain ⟨U, hU, hηU, hUs⟩ := hs.2 h.1
      obtain ⟨V, hV, hηV, hVt⟩ := ht.2 h.2
      refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, ?_⟩
      rw [Set.compl_union]
      exact Set.inter_subset_inter hUs hVt
  | compl s _ hs =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact hs.2 h
    · obtain ⟨U, hU, hηU, hUs⟩ := hs.1 (not_not.mp h)
      exact ⟨U, hU, hηU, by rwa [compl_compl]⟩

/-- The hyperplane of a vector `g` of `M` corresponds to the hyperplane of the linear form of its
coordinates. -/
private theorem projHomeomorph_preimage_linearSubspace {M : Type u} [AddCommGroup M] [Module k M]
    (b : Module.Basis (Fin (K + 1)) k M) (g : M) :
    projHomeomorph b ⁻¹' ProjectiveSpaceOfModule.linearSubspace k M (k ∙ g) =
      ((Stacks.ProjectiveSpace.hyperplane (linearForm (b.repr g))).support :
        Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) := by
  ext x
  rw [Set.mem_preimage, ProjectiveSpaceOfModule.mem_linearSubspace_iff,
    Submodule.span_singleton_le_iff_mem, ProjectiveSpaceOfModule.mem_pointSubmodule_iff,
    ι_mem_projHomeomorph_iff, mem_support_hyperplane_iff]

/-- The basis of `kᴷ⁺¹`, indexed through `ULift`, that the dimension count is stated in. -/
private noncomputable abbrev uliftBasis (k : Type u) [Field k] (K : ℕ) :
    Module.Basis (Fin (K + 1)) k (ULift.{u} (Fin (K + 1)) → k) :=
  (Pi.basisFun k (ULift.{u} (Fin (K + 1)))).reindex Equiv.ulift

/-- The coordinates of a vector in `uliftBasis`. -/
private theorem uliftBasis_repr (g : ULift.{u} (Fin (K + 1)) → k) :
    (uliftBasis k K).repr g = g ∘ ULift.up := by
  ext i
  simp [uliftBasis]

/-- **General linear sections of constructible subsets of `ℙᴷ_k`**, in the model
`Proj k[T₀, …, T_K]`: the dimension count of
`MMP.exists_ne_zero_forall_eval_ne_zero_inter_hyperplanes` transported along `projHomeomorph`. -/
theorem exists_polynomial_inter_hyperplanes [IsAlgClosed k] [CharZero k] {υ : Type*}
    [Finite υ] (W : υ → Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))
    (hW : ∀ u, Topology.IsConstructible (W u)) (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × Fin (K + 1)) k, P ≠ 0 ∧
      ∀ f : Fin c → Fin (K + 1) → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 → ∀ u,
        (topologicalKrullDim (W u) < c →
          W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f i))).support :
            Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) = ∅) ∧
        ((c : WithBot ℕ∞) ≤ topologicalKrullDim (W u) →
          (W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f i))).support :
            Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))).Nonempty ∧
          topologicalKrullDim ↥(W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane
              (linearForm (f i))).support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))) + c =
            topologicalKrullDim (W u)) := by
  classical
  set e := projHomeomorph (uliftBasis k K)
  obtain ⟨P, hP0, hP⟩ := MMP.exists_ne_zero_forall_eval_ne_zero_inter_hyperplanes k
    (ι := ULift.{u} (Fin (K + 1))) (fun u => e '' W u)
    (fun u => isConstructible_image_homeomorph e (hW u)) c
  refine ⟨MvPolynomial.rename (fun p : Fin c × ULift.{u} (Fin (K + 1)) => (p.1, p.2.down)) P,
    ?_, fun f hf u => ?_⟩
  · refine fun h => hP0 (MvPolynomial.rename_injective _ ?_ (h.trans (map_zero _).symm))
    rintro ⟨i, ⟨j⟩⟩ ⟨i', ⟨j'⟩⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  set f' : Fin c → ULift.{u} (Fin (K + 1)) → k := fun i j => f i j.down
  have hf' : MvPolynomial.eval (fun p => f' p.1 p.2) P ≠ 0 := by
    rwa [MvPolynomial.eval_rename] at hf
  have hcut : e '' (W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f i))).support :
      Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))) =
      e '' W u ∩ ⋂ i, ProjectiveSpaceOfModule.linearSubspace k _ (k ∙ f' i) := by
    rw [Set.image_inter e.injective, Set.image_iInter e.bijective]
    congr 1
    refine Set.iInter_congr fun i => ?_
    have hfi : f i = (uliftBasis k K).repr (f' i) := by
      rw [uliftBasis_repr]
      rfl
    rw [hfi, ← projHomeomorph_preimage_linearSubspace]
    exact e.image_preimage _
  obtain ⟨h1, h2⟩ := hP f' hf' u
  rw [topologicalKrullDim_image_of_isEmbedding e.isEmbedding] at h1 h2
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · have := h1 hlt
    rw [← hcut] at this
    exact Set.image_eq_empty.mp this
  · obtain ⟨hne, hdim⟩ := h2 hle
    rw [← hcut] at hne hdim
    rw [topologicalKrullDim_image_of_isEmbedding e.isEmbedding] at hdim
    exact ⟨Set.image_nonempty.mp hne, hdim⟩

/-- The image of a quasi-compact morphism of finite presentation from an irreducible scheme to a
quasi-compact quasi-separated scheme locally of finite type over a field has the dimension of its
closure. -/
private theorem topologicalKrullDim_closure_range_le_range {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IrreducibleSpace X] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (g : X ⟶ Y) [QuasiCompact g] [LocallyOfFinitePresentation g] :
    topologicalKrullDim (closure (Set.range g)) ≤ topologicalKrullDim (Set.range g) := by
  set F : Closeds Y := ⟨closure (Set.range g), isClosed_closure⟩
  set I := Scheme.IdealSheafData.vanishingIdeal F
  set j := I.subschemeι
  have hrange : Set.range j = closure (Set.range g) := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hirr : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ X).image g g.continuous.continuousOn).closure
  have hemb := (IsClosedImmersion.isClosedEmbedding j).isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    haveI : IrreducibleSpace (Set.range j) := Subtype.irreducibleSpace (hrange ▸ hirr)
    exact (hemb.toHomeomorph.irreducibleSpace_iff).mpr inferInstance
  have hη : ∀ U : Set I.subscheme, IsOpen U → U.Nonempty → genericPoint I.subscheme ∈ U :=
    fun U hU hne => ((genericPoint_spec I.subscheme).mem_open_set_iff hU).mpr (by simpa using hne)
  have hS : Topology.IsConstructible (j ⁻¹' Set.range g) := by
    have := g.isConstructible_image (s := Set.univ) .univ
    rw [Set.image_univ] at this
    exact j.isConstructible_preimage this
  have hηS : genericPoint I.subscheme ∈ j ⁻¹' Set.range g := by
    have h1 : IsGenericPoint (j (genericPoint I.subscheme)) (closure (Set.range g)) := by
      have := (genericPoint_spec I.subscheme).image j.continuous
      rwa [Set.image_univ, hrange, closure_closure] at this
    have h2 : IsGenericPoint (g (genericPoint X)) (closure (Set.range g)) := by
      have := (genericPoint_spec X).image g.continuous
      rwa [Set.image_univ] at this
    rw [Set.mem_preimage, h1.eq h2]
    exact ⟨_, rfl⟩
  obtain ⟨U, hU, hηU, hUS⟩ := (exists_isOpen_of_isConstructible hη hS).1 hηS
  calc topologicalKrullDim (closure (Set.range g))
      = topologicalKrullDim (Set.range j) := by rw [hrange]
    _ = topologicalKrullDim I.subscheme :=
        (IsHomeomorph.topologicalKrullDim_eq _ hemb.toHomeomorph.isHomeomorph).symm
    _ = topologicalKrullDim U :=
        topologicalKrullDim_eq_of_isOpen k I.subscheme (j ≫ sY) U hU ⟨_, hηU⟩
    _ = topologicalKrullDim (j '' U) := (topologicalKrullDim_image_of_isEmbedding hemb U).symm
    _ ≤ topologicalKrullDim (Set.range g) :=
        topologicalKrullDim_le_of_subset (Set.image_subset_iff.mpr hUS)

variable {V : Scheme.{u}} [V.Over (Spec (.of k))] (φ : V ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))

/-- The pullback `φ^*𝒪(1)`. -/
noncomputable abbrev pullTwist : V.Modules := (Scheme.Modules.pullback φ).obj (twistOne k K)

/-- The system `φ^*T₀, …, φ^*T_K` of sections of `φ^*𝒪(1)`. -/
noncomputable def pulledSystem : Fin (K + 1) → Γ(pullTwist φ, ⊤) := fun i =>
  pullbackGlobalSections φ (twistOne k K)
    (formSection ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩)

variable {φ}

/-- The member `∑ᵢ aᵢ φ^*Tᵢ` of the pulled-back system is the pullback of `∑ᵢ aᵢ Tᵢ`. -/
theorem systemSection_pulledSystem
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k))
    (a : Fin (K + 1) → k) :
    systemSection (pulledSystem φ) a =
      pullbackGlobalSections φ (twistOne k K) (formSection (linearForm a)) := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Over (Spec (.of k)) :=
    ⟨Stacks.ProjectiveCohomology.projModelToSpec k K⟩
  have h := map_sum (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ k φ
    (twistOne k K) hφ) (fun i => a i • formSection
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) Finset.univ
  simp only [map_smul,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ_apply] at h
  rw [systemSection_apply, formSection_linearForm]
  exact h.symm

/-- **The member of the pulled-back system with coefficients `a` cuts out `φ⁻¹(H_a)`.** -/
theorem zeroScheme_pulledSystem
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k))
    (a : Fin (K + 1) → k) :
    zeroScheme V (pullTwist φ) (systemSection (pulledSystem φ) a) = hyperplaneSection φ a := by
  rw [systemSection_pulledSystem hφ]
  exact Stacks.Divisors.zeroScheme_pullback φ (twistOne k K) _

/-- A member of the pulled-back system does not vanish at `y` exactly when its linear form is
outside the prime of `φ(y)`. -/
theorem mem_nonvanishingOpen_pulledSystem_iff
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k))
    (a : Fin (K + 1) → k) (y : V) :
    y ∈ nonvanishingOpen V (pullTwist φ) (systemSection (pulledSystem φ) a) ↔
      (linearForm a : MvPolynomial (Fin (K + 1)) k) ∉ (φ y).asHomogeneousIdeal := by
  rw [systemSection_pulledSystem hφ,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
  exact mem_nonvanishingOpen_formSection_iff _ (φ y)

/-- Some coordinate does not vanish at a point of `ℙᴷ_k`. -/
theorem exists_X_notMem (x : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :
    ∃ i, (MvPolynomial.X i : MvPolynomial (Fin (K + 1)) k) ∉ x.asHomogeneousIdeal := by
  obtain ⟨f, hf⟩ :=
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.exists_mem_nonvanishingLocus_degreeSection
      (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) k)
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (K + 1)) k) x
  have hf' := (mem_nonvanishingOpen_formSection_iff f x).mp hf
  by_contra h
  push Not at h
  apply hf'
  have hspan : (f : MvPolynomial (Fin (K + 1)) k) ∈
      Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (K + 1)))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hdeg := f.2 (MvPolynomial.mem_support_iff.mp hm)
    by_contra hne
    push Not at hne
    have : m = 0 := Finsupp.ext fun i => hne i (Set.mem_univ i)
    subst this
    simp at hdeg
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨i, -, rfl⟩
  exact h i

/-- The linear form of a standard basis vector is a coordinate. -/
theorem linearForm_single (i : Fin (K + 1)) :
    linearForm (Pi.single i (1 : k)) = ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩ := by
  apply Subtype.ext
  simp [coe_linearForm, Pi.single_apply]

/-- **The pulled-back system generates `φ^*𝒪(1)`.** -/
theorem iSup_nonvanishingOpen_pulledSystem
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k)) :
    ⨆ c : Fin (K + 1) → k, nonvanishingOpen V (pullTwist φ) (systemSection (pulledSystem φ) c) =
      ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨i, hi⟩ := exists_X_notMem (φ y)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single i 1, ?_⟩
  rw [mem_nonvanishingOpen_pulledSystem_iff hφ, linearForm_single]
  exact hi

/-- `ℙᴷ_k` is a Jacobson space. -/
private theorem jacobsonSpace_projectiveSpace : JacobsonSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :=
  LocallyOfFiniteType.jacobsonSpace (Stacks.ProjectiveCohomology.projModelToSpec k K)

/-- A `k`-morphism from a scheme locally of finite type over `k` to `ℙᴷ_k` is locally of finite
type. -/
private theorem locallyOfFiniteType_of_comp_eq [LocallyOfFiniteType (V ↘ Spec (.of k))]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k)) :
    LocallyOfFiniteType φ := by
  have : LocallyOfFiniteType (φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K) := by
    rw [hφ]; infer_instance
  exact LocallyOfFiniteType.of_comp (f := φ)
    (g := Stacks.ProjectiveCohomology.projModelToSpec k K) this

/-- **At closed points, the morphism of the pulled-back system is `φ`** read through
`projHomeomorph`: both send a closed point `y` to the closed point cut out by the forms vanishing
at `φ(y)`. -/
private theorem morphismOfGeneratingSections_pulledSystem_apply [IsAlgClosed k]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k)) {y : V}
    (hy : IsClosed ({y} : Set V)) :
    morphismOfGeneratingSections k (Fin (K + 1) → k) (pullTwist φ)
        (systemSection (pulledSystem φ)) (iSup_nonvanishingOpen_pulledSystem hφ) y =
      projHomeomorph (Pi.basisFun k (Fin (K + 1))) (φ y) := by
  haveI := jacobsonSpace_projectiveSpace (k := k) (K := K)
  haveI := locallyOfFiniteType_of_comp_eq hφ
  have hcl : IsClosed ({φ y} : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hy
  set e := projHomeomorph (k := k) (K := K) (Pi.basisFun k (Fin (K + 1)))
  have hq : IsClosed ({e (φ y)} : Set (projectiveSpaceOfModule k (Fin (K + 1) → k))) := by
    rw [← Set.image_singleton]
    exact e.isClosedMap _ hcl
  obtain ⟨f, hf0, hf, -⟩ := ProjectiveSpaceOfModule.exists_dual_of_closedPoint k _ ⟨e (φ y), hq⟩
  have key : ∀ v, f v = 0 →
      y ∉ nonvanishingOpen V (pullTwist φ) (systemSection (pulledSystem φ) v) := by
    intro v hv
    rw [mem_nonvanishingOpen_pulledSystem_iff hφ, not_not]
    have h := (hf v).mpr hv
    rw [ι_mem_projHomeomorph_iff] at h
    have hr : ⇑((Pi.basisFun k (Fin (K + 1))).repr v) = v := funext fun i => by simp
    rwa [hr] at h
  rw [morphismOfGeneratingSections_base_eq k _ _ _ _ y hf0 key]
  have hmem : e (φ y) ∈ ProjectiveSpaceOfModule.linearSubspace k _ (LinearMap.ker f) :=
    (ProjectiveSpaceOfModule.mem_linearSubspace_iff _ _ _ _).mpr fun v hv => (hf v).mpr hv
  rw [ProjectiveSpaceOfModule.linearSubspace_ker k _ f hf0] at hmem
  exact hmem.symm

/-- **The image of the morphism of the pulled-back system is at least as big as `φ(V)`**: it
contains the images of the closed points, which are dense, and an image has the dimension of its
closure. -/
private theorem topologicalKrullDim_closure_range_le_range_morphismOfGeneratingSections
    [IsAlgClosed k] [IsVariety k (V ↘ Spec (.of k))]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k)) :
    topologicalKrullDim (closure (Set.range φ)) ≤
      topologicalKrullDim (Set.range (morphismOfGeneratingSections k (Fin (K + 1) → k)
        (pullTwist φ) (systemSection (pulledSystem φ))
        (iSup_nonvanishingOpen_pulledSystem hφ))) := by
  set m := morphismOfGeneratingSections k (Fin (K + 1) → k)
    (pullTwist φ) (systemSection (pulledSystem φ)) (iSup_nonvanishingOpen_pulledSystem hφ)
  set e := projHomeomorph (k := k) (K := K) (Pi.basisFun k (Fin (K + 1)))
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace (V ↘ Spec (.of k))
  have hsub : Set.range (e ∘ φ) ⊆ closure (Set.range m) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ closure (closedPoints V) := by rw [closure_closedPoints]; trivial
    refine map_mem_closure (e.continuous.comp φ.continuous) hy fun z hz => ?_
    exact ⟨z, morphismOfGeneratingSections_pulledSystem_apply hφ hz⟩
  haveI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  haveI := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  haveI : IsNoetherian V := {}
  haveI :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k (Fin (K + 1) → k))
  haveI : CompactSpace (projectiveSpaceOfModule k (Fin (K + 1) → k)) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k _)
  haveI : QuasiSeparatedSpace (projectiveSpaceOfModule k (Fin (K + 1) → k)) := inferInstance
  haveI : LocallyOfFiniteType m := by
    have h := morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec
      (k := k) (V := Fin (K + 1) → k) (L := pullTwist φ)
      (systemSection (pulledSystem φ)) (iSup_nonvanishingOpen_pulledSystem hφ)
    have : LocallyOfFiniteType (m ≫ projectiveSpaceOfModuleToSpec k (Fin (K + 1) → k)) := by
      rw [h]; infer_instance
    exact locallyOfFiniteType_of_comp m (projectiveSpaceOfModuleToSpec k (Fin (K + 1) → k))
  calc topologicalKrullDim (closure (Set.range φ))
      = topologicalKrullDim (e '' closure (Set.range φ)) :=
        (topologicalKrullDim_image_of_isEmbedding e.isEmbedding _).symm
    _ ≤ topologicalKrullDim (closure (Set.range m)) := by
        refine topologicalKrullDim_le_of_subset ?_
        rw [e.image_closure, ← Set.range_comp]
        exact closure_minimal hsub isClosed_closure
    _ ≤ topologicalKrullDim (Set.range m) :=
        topologicalKrullDim_closure_range_le_range (projectiveSpaceOfModuleToSpec k _) m

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
private theorem isInvertible_of_isInvertibleModule {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- **Purity of the zero scheme on an irreducible closed subset.** Let `Z` be an irreducible
closed subset of a scheme locally of finite type over a field and `s` a section of an invertible
module not vanishing identically on `Z`. Every irreducible component `T` of `Z ∩ Z(s)` satisfies
`dim T + 1 = dim Z`: on the integral closed subscheme supported on `Z` the pulled-back section
cuts out an effective Cartier divisor, whose components have codimension one. -/
private theorem topologicalKrullDim_add_one_of_maximal_zeroScheme {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) {Z : Set X} (hZc : IsClosed Z)
    (hZi : IsIrreducible Z)
    (hnot : ¬ Z ⊆
      ((haveI := isInvertible_of_isInvertibleModule L; zeroScheme X L s).support : Set X))
    {T : Set X}
    (hT : Maximal (fun T => IsIrreducible T ∧ T ⊆ Z ∩
      ((haveI := isInvertible_of_isInvertibleModule L; zeroScheme X L s).support : Set X)) T) :
    topologicalKrullDim T + 1 = topologicalKrullDim Z := by
  haveI := isInvertible_of_isInvertibleModule L
  set H : Set X := ((zeroScheme X L s).support : Set X) with hH
  have hHc : IsClosed H := (zeroScheme X L s).support.isClosed
  set x := hZi.genericPoint
  have hxZ : closure {x} = Z := by rw [hZi.genericPoint_closure_eq, hZc.closure_eq]
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  haveI : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set j := I.subschemeι
  have hrange : Set.range j = Z := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hxZ
  have hjemb := IsClosedImmersion.isClosedEmbedding j
  set s' := pullbackGlobalSections j L s
  haveI := isInvertible_of_isInvertibleModule ((Scheme.Modules.pullback j).obj L)
  set D := zeroScheme I.subscheme ((Scheme.Modules.pullback j).obj L) s'
  have hD : D = (zeroScheme X L s).comap j := Stacks.Divisors.zeroScheme_pullback j L s
  have hDsupp : (D.support : Set I.subscheme) = j ⁻¹' H := by
    rw [hD, Scheme.IdealSheafData.support_comap]
    rfl
  have hs' : s' ≠ 0 := by
    intro h0
    apply hnot
    rw [← hrange]
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ (D.support : Set I.subscheme) := by
      by_contra hz
      have h1 := (mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme _ s' z).mpr hz
      change z ∈ Stacks.Ample.nonvanishingLocus _ s' at h1
      rw [h0, Stacks.Ample.nonvanishingLocus_zero] at h1
      exact h1
    rw [hDsupp] at hz
    exact hz
  have hDcart := isEffectiveCartierDivisor_zeroScheme_of_ne_zero _ s' hs'
  have hc : IsClosed (Z ∩ H) := hZc.inter hHc
  have hTsub := hT.prop.2
  have hTclosed : IsClosed T := by
    have : closure T ⊆ T := hT.2 ⟨hT.prop.1.closure, closure_minimal hTsub hc⟩ subset_closure
    exact closure_subset_iff_isClosed.mp this
  set η := hT.prop.1.genericPoint
  have hηT : closure {η} = T := by rw [hT.prop.1.genericPoint_closure_eq, hTclosed.closure_eq]
  have hηmem : η ∈ T := hηT ▸ subset_closure rfl
  set ι := D.subschemeι ≫ j
  have hιemb : Topology.IsClosedEmbedding ι := IsClosedImmersion.isClosedEmbedding ι
  have hιrange : Set.range ι = Z ∩ H := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, D.range_subschemeι]
    change j '' (D.support : Set I.subscheme) = Z ∩ H
    rw [hDsupp, Set.image_preimage_eq_range_inter, hrange]
  obtain ⟨ξ, hξ⟩ : η ∈ Set.range ι := hιrange ▸ hTsub hηmem
  have hC : closure {ξ} ∈ irreducibleComponents D.subscheme := by
    refine ⟨isIrreducible_singleton.closure, fun C' hC' hle => ?_⟩
    have hirr : IsIrreducible (closure (ι '' C')) :=
      (hC'.image ι hιemb.continuous.continuousOn).closure
    have hsub : closure (ι '' C') ⊆ Z ∩ H := by
      refine closure_minimal ?_ hc
      rintro _ ⟨c, -, rfl⟩
      rw [← hιrange]
      exact ⟨c, rfl⟩
    have hTle : T ⊆ closure (ι '' C') := by
      rw [← hηT]
      refine closure_minimal ?_ isClosed_closure
      rintro _ rfl
      exact subset_closure ⟨ξ, hle (subset_closure rfl), hξ⟩
    have heq : closure (ι '' C') ⊆ T := hT.2 ⟨hirr, hsub⟩ hTle
    intro c hc'
    rw [hιemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hξ, hηT]
    exact heq (subset_closure ⟨c, hc', rfl⟩)
  haveI : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have hdim1 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hDcart ξ
    ⟨⟨_, hC⟩, isGenericPoint_closure⟩
  rw [ringKrullDim_stalk_eq_coheight] at hdim1
  have hco : Order.coheight (D.subschemeι ξ) = 1 := by exact_mod_cast hdim1
  have hformula := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (j ≫ sX)
    (D.subschemeι ξ)
  rw [hco] at hformula
  have himg : j '' closure {D.subschemeι ξ} = T := by
    rw [← hjemb.isClosedMap.closure_image_eq_of_continuous hjemb.continuous, Set.image_singleton]
    rw [← hηT, ← hξ]
    rfl
  have hdimT : topologicalKrullDim T = topologicalKrullDim (closure {D.subschemeι ξ}) := by
    rw [← himg]
    exact topologicalKrullDim_image_of_isEmbedding hjemb.isEmbedding _
  have hdimZ : topologicalKrullDim Z = topologicalKrullDim I.subscheme := by
    rw [← hrange]
    exact (IsHomeomorph.topologicalKrullDim_eq _
          (IsClosedImmersion.isClosedEmbedding j).isEmbedding.toHomeomorph.isHomeomorph).symm
  rw [hdimT, hdimZ, ← hformula]
  rfl

/-- Subsets of `ℙᴷ_k` have dimension at most `K`. -/
private theorem topologicalKrullDim_le_of_projectiveSpace (S : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) :
    topologicalKrullDim S ≤ K := by
  calc topologicalKrullDim S ≤ topologicalKrullDim (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :=
        topologicalKrullDim_subspace_le _ S
    _ = topologicalKrullDim (projectiveSpaceOfModule k (Fin (K + 1) → k)) :=
        (projHomeomorph (Pi.basisFun k (Fin (K + 1)))).isHomeomorph.topologicalKrullDim_eq _
    _ = K := topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (k := k)
        (V := Fin (K + 1) → k) (n := K) (by simp)

/-- The support of `φ⁻¹(H_a)` is the preimage of the hyperplane `H_a`. -/
theorem coe_support_hyperplaneSection (a : Fin (K + 1) → k) :
    ((hyperplaneSection φ a).support : Set V) =
      φ ⁻¹' (Stacks.ProjectiveSpace.hyperplane (linearForm a)).support := by
  rw [hyperplaneSection, Scheme.IdealSheafData.support_comap]
  rfl

/-- **A hyperplane cutting `φ(Z)` properly pulls back to a divisor cutting `Z` properly.** If `H`
misses `φ(Z)` when `φ(Z)` has dimension zero and otherwise meets it in codimension one, then
`φ⁻¹(H)` does not contain `Z`, misses `Z` when `φ(Z)` is a point, and otherwise meets `Z` in a
nonempty set all of whose irreducible components have codimension one in `Z`. -/
theorem hyperplaneSection_inter_of_image_inter_hyperplane
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k))
    {Z : Set V} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (a : Fin (K + 1) → k)
    (hlt : topologicalKrullDim (φ '' Z) < 1 → φ '' Z ∩
      (Stacks.ProjectiveSpace.hyperplane (linearForm a)).support = ∅)
    (hge : 1 ≤ topologicalKrullDim (φ '' Z) →
      (φ '' Z ∩ (Stacks.ProjectiveSpace.hyperplane (linearForm a)).support).Nonempty ∧
      topologicalKrullDim ↥(φ '' Z ∩ (Stacks.ProjectiveSpace.hyperplane (linearForm a)).support)
        + 1 = topologicalKrullDim (φ '' Z)) :
    ¬ Z ⊆ (hyperplaneSection φ a).support ∧
      ((φ '' Z).Subsingleton → Z ∩ (hyperplaneSection φ a).support = ∅) ∧
      (¬ (φ '' Z).Subsingleton → ∀ T : Set V,
        Maximal (fun T => IsIrreducible T ∧ T ⊆ Z ∩ (hyperplaneSection φ a).support) T →
          topologicalKrullDim T + 1 = topologicalKrullDim Z) ∧
      (¬ (φ '' Z).Subsingleton → (Z ∩ (hyperplaneSection φ a).support).Nonempty) := by
  have hsupp := coe_support_hyperplaneSection (φ := φ) a
  have hpos : ¬ (φ '' Z).Subsingleton → (1 : WithBot ℕ∞) ≤ topologicalKrullDim (φ '' Z) :=
    one_le_topologicalKrullDim_of_isIrreducible (hZi.image φ φ.continuous.continuousOn)
  have hempty : (φ '' Z).Subsingleton → Z ∩ (hyperplaneSection φ a).support = ∅ := by
    intro hsub
    rw [hsupp, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzH⟩
    exact (Set.eq_empty_iff_forall_notMem.mp (hlt (topologicalKrullDim_lt_one_of_subsingleton
      hsub))) (φ z) ⟨⟨z, hz, rfl⟩, hzH⟩
  have hnot : ¬ Z ⊆ (hyperplaneSection φ a).support := by
    intro hsub
    by_cases hs1 : (φ '' Z).Subsingleton
    · exact hZi.nonempty.ne_empty (Set.inter_eq_left.mpr hsub ▸ hempty hs1)
    · have hdim := (hge (hpos hs1)).2
      rw [Set.inter_eq_left.mpr (Set.image_subset_iff.mpr (hsupp ▸ hsub))] at hdim
      exact add_one_ne_self (topologicalKrullDim_le_of_projectiveSpace _) (hpos hs1) hdim
  refine ⟨hnot, hempty, fun _ T hT => ?_, fun hs1 => ?_⟩
  · haveI := isInvertible_of_isInvertibleModule (pullTwist φ)
    rw [← zeroScheme_pulledSystem hφ] at hnot hT
    exact topologicalKrullDim_add_one_of_maximal_zeroScheme (V ↘ Spec (.of k)) (pullTwist φ) _
      hZc hZi hnot hT
  · obtain ⟨⟨_, ⟨z, hz, rfl⟩, hzH⟩, -⟩ := hge (hpos hs1)
    exact ⟨z, hz, hsupp ▸ hzH⟩

/-- **General hyperplane sections.** Let `k` be algebraically closed of characteristic zero, `V` a
variety over `k`, `φ : V ⟶ ℙᴷ_k` a `k`-morphism and `Z_l ⊆ V` (`l ∈ ι`, `ι` finite) irreducible
closed subsets. There is a dense open `U` of the dual projective space such that for every
nonzero `a` with `[a] ∈ U`, writing `φ⁻¹(H) = hyperplaneSection φ a`: `φ⁻¹(H)` is smooth over `k`
if `V` is; `φ⁻¹(H)` is irreducible if `dim closure (φ(V)) ≥ 2`; and for every `l`,
`Z_l ⊄ φ⁻¹(H)`, `Z_l ∩ φ⁻¹(H) = ∅` if `φ(Z_l)` is a point, every irreducible component of
`Z_l ∩ φ⁻¹(H)` has dimension `dim Z_l - 1` otherwise, and `Z_l ∩ φ⁻¹(H) ≠ ∅` if moreover `Z_l`
is proper over `k`. Moreover, for finitely many constructible `W_u ⊆ ℙᴷ_k` and `c : ℕ`, there is
a nonzero polynomial `P` in the coefficients of `c` linear forms `f_1, …, f_c` such that whenever
`P(f) ≠ 0`, for every `u` the cut `W_u ∩ V(f_1) ∩ ⋯ ∩ V(f_c)` is empty if `dim W_u < c`, and
otherwise is nonempty of dimension `dim W_u - c`. -/
@[mmp "lem_mmp_foundation_fa2_general_hyperplane"]
public theorem exists_dense_open_hyperplaneSection (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] {V : Scheme.{u}} [V.Over (Spec (.of k))] [IsVariety k (V ↘ Spec (.of k))]
    {K : ℕ} (φ : V ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k K = V ↘ Spec (.of k))
    {ι : Type*} [Finite ι] (Z : ι → Set V) (hZc : ∀ l, IsClosed (Z l))
    (hZi : ∀ l, IsIrreducible (Z l))
    {υ : Type*} [Finite υ] (W : υ → Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))
    (hW : ∀ u, Topology.IsConstructible (W u)) (c : ℕ) :
    (∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) ∧
      ∀ (a : Fin (K + 1) → k) (ha : a ≠ 0), dualPoint a ha ∈ U →
        (Smooth (V ↘ Spec (.of k)) →
          Smooth ((hyperplaneSection φ a).subschemeι ≫ V ↘ Spec (.of k))) ∧
        ((2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range φ)) →
          IsIrreducible ((hyperplaneSection φ a).support : Set V)) ∧
        ∀ l, ¬ Z l ⊆ (hyperplaneSection φ a).support ∧
          ((φ '' Z l).Subsingleton → Z l ∩ (hyperplaneSection φ a).support = ∅) ∧
          (¬ (φ '' Z l).Subsingleton → ∀ T : Set V,
            Maximal (fun T => IsIrreducible T ∧ T ⊆ Z l ∩ (hyperplaneSection φ a).support) T →
              topologicalKrullDim T + 1 = topologicalKrullDim (Z l)) ∧
          (IsProper ((Scheme.IdealSheafData.vanishingIdeal ⟨Z l, hZc l⟩).subschemeι ≫
              V ↘ Spec (.of k)) →
            ¬ (φ '' Z l).Subsingleton → (Z l ∩ (hyperplaneSection φ a).support).Nonempty)) ∧
    ∃ P : MvPolynomial (Fin c × Fin (K + 1)) k, P ≠ 0 ∧
      ∀ f : Fin c → Fin (K + 1) → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 → ∀ u,
        (topologicalKrullDim (W u) < c →
          W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f i))).support :
            Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) = ∅) ∧
        ((c : WithBot ℕ∞) ≤ topologicalKrullDim (W u) →
          (W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f i))).support :
            Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))).Nonempty ∧
          topologicalKrullDim ↥(W u ∩ ⋂ i, ((Stacks.ProjectiveSpace.hyperplane
              (linearForm (f i))).support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)))) + c =
            topologicalKrullDim (W u)) := by
  classical
  refine ⟨?_, exists_polynomial_inter_hyperplanes W hW c⟩
  have hs := iSup_nonvanishingOpen_pulledSystem hφ
  -- smoothness of the general member
  obtain ⟨-, U₁, hU₁, hsm⟩ := @exists_dense_open_smooth_zeroScheme k _ K V _ (pullTwist φ) _ _ _ _
    (pulledSystem φ) hs PEmpty _ (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim)
  -- irreducibility of the general member
  obtain ⟨U₂, hU₂, hirr⟩ :
      ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K))) ∧
      ∀ (a : Fin (K + 1) → k) (ha : a ≠ 0), dualPoint a ha ∈ U →
        (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range φ)) →
          IsIrreducible ((hyperplaneSection φ a).support : Set V) := by
    by_cases h2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range φ))
    · obtain ⟨-, U, hU, hint⟩ := exists_dense_open_geometricallyIntegral_zeroScheme
        (pulledSystem φ) hs
        (h2.trans (topologicalKrullDim_closure_range_le_range_morphismOfGeneratingSections hφ))
      refine ⟨U, hU, fun a ha hmem _ => ?_⟩
      have h := (hint a ha hmem).2
      rw [zeroScheme_pulledSystem hφ] at h
      rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (Scheme.Hom.continuous _).continuousOn
    · exact ⟨⊤, dense_univ, fun a ha _ h => absurd h h2⟩
  -- the dimension count for the images of the `Z l`
  haveI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
  haveI := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of k))
  haveI : IsNoetherian V := {}
  haveI := LocallyOfFiniteType.isLocallyNoetherian (Stacks.ProjectiveCohomology.projModelToSpec k K)
  haveI : CompactSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) :=
    QuasiCompact.compactSpace_of_compactSpace (Stacks.ProjectiveCohomology.projModelToSpec k K)
  haveI : QuasiSeparatedSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k K)) := inferInstance
  haveI := locallyOfFiniteType_of_comp_eq hφ
  have hcons : ∀ l, Topology.IsConstructible (φ '' Z l) := fun l =>
    φ.isConstructible_image (Topology.isConstructible_compl.mp
      ((NoetherianSpace.isCompact _).isConstructible (hZc l).isOpen_compl))
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_inter_hyperplanes (fun l => φ '' Z l) hcons 1
  obtain ⟨U₃, hU₃, hgood⟩ := exists_dense_open_of_polynomial hP0
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, ?_, fun a ha hmem => ⟨fun hV => ?_, hirr a ha hmem.1.2, fun l => ?_⟩⟩
  · rw [Opens.coe_inf, Opens.coe_inf]
    exact (hU₁.inter_of_isOpen_left hU₂ U₁.isOpen).inter_of_isOpen_left hU₃
      (U₁.isOpen.inter U₂.isOpen)
  · have h := (hsm a ha hmem.1.1).1 hV
    rwa [zeroScheme_pulledSystem hφ] at h
  obtain ⟨t, ht, hPt⟩ := hgood a ha hmem.2
  have hH := hP (fun _ => t • a) hPt l
  rw [Set.iInter_const, support_hyperplane_linearForm_smul a ht, Nat.cast_one] at hH
  obtain ⟨hnot, hempty, hpure, hne⟩ :=
    hyperplaneSection_inter_of_image_inter_hyperplane hφ (hZc l) (hZi l) a hH.1 hH.2
  exact ⟨hnot, hempty, hpure, fun _ => hne⟩

end MMP.Threefold.Bridges
