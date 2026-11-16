module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import MMP.AlgebraicGeometry.Divisor.Cycles
import MMP.AlgebraicGeometry.ProjectiveSpace.Hyperplane
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Geometrically.BertiniGenericFibres
import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericConstancy

/-!
# General hyperplane sections, and spreading out geometric integrality of fibres

This file collects two Bertini-type genericity statements.

**General hyperplane sections.** Let `k` be an algebraically closed field of characteristic zero
and `φ : X ⟶ ℙᴺ_k` a `k`-immersion of a variety `X`. Let `f : W ⟶ X` be a `k`-morphism from a
smooth variety `W`, and `S_α ⟶ W` finitely many smooth locally closed subschemes of `W`. For a
general hyperplane `H ⊆ ℙᴺ_k` (one in a dense open of the dual projective space), with
hyperplane section `X_H = φ⁻¹(H)`: `X_H` is normal if `X` is; `f⁻¹(X_H)` is smooth over `k`;
every trace `f⁻¹(X_H) ∩ S_α` is smooth over `k` and nowhere dense in `S_α`; and `X_H` contains
no irreducible component of any member of a given finite family of subsets of `X`.

The coordinates `T₀, …, T_N` of `𝒪(1)` pull back along any `k`-morphism `ψ : Z ⟶ ℙᴺ_k` to
sections generating `ψ^* 𝒪(1)`, and the zero scheme of `∑ᵢ cᵢ ψ^* Tᵢ` is `ψ⁻¹(V(∑ᵢ cᵢ Tᵢ))`, so
Bertini's theorems for free systems apply to hyperplane sections. A hyperplane passes through a
given point only for `[c]` in a proper linear subspace of the dual space, so a general hyperplane
misses any finite set of points: the generic points of the components of the strata (giving
transversality) and of the closures of the maximal irreducible subsets of the given sets.

**Generic fibres of proper families.** Let `R` be a domain of finite type over a field `k₀` of
characteristic zero and `f : X ⟶ Spec R` proper with geometrically integral generic fibre.
Over a nonempty principal open `D(r)` every fibre is geometrically integral of the dimension of
the generic fibre; if the generic fibre is moreover normal, these fibres are geometrically
normal as well. Geometric irreducibility, geometric reducedness and the fibre dimension each
spread from the generic fibre to a nonempty open of the base; in the normal case, geometric
normality spreads in addition by generic normality.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_hyperplaneSection_stratified`: Bertini for general
  hyperplane sections.
* `MMP.exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper`: normal geometrically
  integral generic fibres of a proper family spread.
* `MMP.exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic`: geometrically
  integral generic fibres of a proper family spread.

## Implementation notes

A hyperplane is `V(∑ᵢ cᵢ Tᵢ)` for a nonzero `c ∈ kᴺ⁺¹`; it is the point
`MMP.Threefold.Bridges.dualPoint c` of the dual projective space, and its section of `X` is the
ideal sheaf `MMP.Threefold.Bridges.hyperplaneSection φ c`. Pullbacks and traces are
`AlgebraicGeometry.Scheme.IdealSheafData.comap`, and a locally closed subscheme is an immersion.
A zero scheme on a smooth scheme that is smooth and nowhere dense is a smooth Cartier divisor,
which is the form of transversality used.

The generic fibre is `f.fiber (genericPoint (Spec R))`. A fibre is geometrically integral
(resp. normal) when `f.fiberToSpecResidueField s` is `GeometricallyIntegral` (resp.
`geometrically IsNormal`), and the dimension of a scheme is `topologicalKrullDim`. The source
proves the non-normal case through the normalization of `X` and the normal case; the spreading
results for geometric irreducibility, reducedness and fibre dimension make that detour
unnecessary.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.4 and the
  proof of 3.39
* [The Stacks Project, Tags 0559, 0578, 05F7, 0FD3](https://stacks.math.columbia.edu)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

/-- `ℙᴺ_k = Proj k[T₀, …, T_N]` as a scheme over `Spec k`, through Stacks' structure morphism
`projToSpecCoeff k N`. -/
private noncomputable local instance instOverProjPolyGrading {k : Type u} [Field k] {N : ℕ} :
    (AlgebraicGeometry.Proj (polyGrading k N)).Over (Spec (.of k)) :=
  ⟨projToSpecCoeff k N⟩

section Bertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule baseRingHom)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] MvPolynomial.gradedAlgebra globalSectionsModule

/-! ### The coordinate sections of `𝒪(1)` -/

section Coordinates

variable {k : Type u} [Field k] {N : ℕ}

variable (k N) in
/-- The twisting sheaf `𝒪(1)` on `ℙᴺ_k`, in the spelling of the hyperplanes. -/
private noncomputable abbrev twistOne : (AlgebraicGeometry.Proj (polyGrading k N)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheafModule
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) ((1 : ℕ) : ℤ)

/-- The global section of `𝒪(1)` of a linear form. -/
private noncomputable def formSection (a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
    Γ(twistOne k N, ⊤) :=
  ProjectiveSpectrum.Proj.degreeSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1 a

/-- The coordinate `Tᵢ` as a global section of `𝒪(1)`. -/
private noncomputable def coordSection (i : Fin (N + 1)) : Γ(twistOne k N, ⊤) :=
  formSection ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩

/-- The value at every point of the constant function `r` on `ℙᴺ_k` is `C r / 1`. -/
private theorem baseRingHom_val (r : k)
    (x : ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) :
    HomogeneousLocalization.val
        ((baseRingHom k (AlgebraicGeometry.Proj (polyGrading k N)) r).1 ⟨x, trivial⟩) =
      algebraMap (MvPolynomial (Fin (N + 1)) k)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r) := by
  unfold baseRingHom
  exact Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val k N r x

/-- The section of a degree-one form is `k`-linear in the form. -/
private theorem smul_formSection (r : k)
    (a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
    r • formSection a = formSection (r • a) := by
  refine Subtype.ext (funext fun x => ?_)
  change HomogeneousLocalization.val
        ((baseRingHom k (AlgebraicGeometry.Proj (polyGrading k N)) r).1 x) •
      LocalizedModule.mk (a : MvPolynomial (Fin (N + 1)) k)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    = LocalizedModule.mk
        ((r • a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
          MvPolynomial (Fin (N + 1)) k)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have hval : HomogeneousLocalization.val
      ((baseRingHom k (AlgebraicGeometry.Proj (polyGrading k N)) r).1 x)
      = Localization.mk (MvPolynomial.C r)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    (baseRingHom_val r x.1).trans
      (Localization.mk_one_eq_algebraMap (MvPolynomial.C r)).symm
  rw [hval, LocalizedModule.mk_smul_mk, one_mul, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul, smul_eq_mul]

/-- `∑ᵢ cᵢ Tᵢ` is the section of the linear form of `c`. -/
private theorem sum_smul_coordSection (c : Fin (N + 1) → k) :
    ∑ i, c i • coordSection (k := k) (N := N) i =
      formSection (linearForm c) := by
  rw [linearForm, formSection, ← ProjectiveSpectrum.Proj.degreeSectionHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => smul_formSection (c i) _

end Coordinates

/-! ### Points off a zero scheme -/

section Nonvanishing

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
private local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- **A point outside the zero scheme of a section lies in its nonvanishing open.** On an affine
open inside a trivializing open of `L`, the ideal of `Z(s)` is generated by the trivializing
function of `s`, and the nonvanishing locus is where that function is a unit. -/
private theorem mem_nonvanishingOpen_of_notMem_support_zeroScheme (s : Γ(L, ⊤)) {x : X}
    (hx : x ∉ (zeroScheme X L s).supportSet) :
    x ∈ nonvanishingOpen X L s := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz (V z).2
  let h : U ⟶ V z := homOfLE hUV
  let e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U) := t.θ U h
  have he : e (L.presheaf.map (homOfLE le_top).op s) =
      X.presheaf.map h.op (Stacks.NonvanishingOpen.trivTop t s) := by
    have hres : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
        L.presheaf.map h.op (L.presheaf.map (homOfLE (le_top : V z ≤ ⊤)).op s) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (Stacks.NonvanishingOpen.triv t h) hres).trans
      (Stacks.NonvanishingOpen.triv_res t (𝟙 (V z)) h h
        (L.presheaf.map (homOfLE (le_top : V z ≤ ⊤)).op s))
  have hideal := zeroScheme_ideal_of_trivialization X L s ⟨U, hU⟩ e _ he
  have hnot : x ∉ X.zeroLocus (U := U) ((zeroScheme X L s).ideal ⟨U, hU⟩) := fun hmem =>
    hx ((Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU).2 hmem)
  rw [hideal, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff,
    not_not] at hnot
  exact (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t s hz).2 <| by
    simpa only [TopCat.Presheaf.germ_res_apply] using (X.mem_basicOpen _ x hxU).mp hnot

end Nonvanishing

/-! ### Hyperplane sections as zero schemes of a free system -/

section Pullback

variable {k : Type u} [Field k] {N : ℕ} {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
  (ψ : Z ⟶ AlgebraicGeometry.Proj (polyGrading k N))

/-- The pullback `ψ^* 𝒪(1)` of the twisting sheaf. -/
private noncomputable abbrev pullTwist : Z.Modules :=
  (Scheme.Modules.pullback ψ).obj (twistOne k N)

private local instance : Stacks.Ample.IsInvertibleModule Z (pullTwist ψ) :=
  Stacks.AlgebraicGeometry.ProjChartRatioPullback.isInvertibleModule_schemeModulesPullback ψ _

private local instance :
    SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property (pullTwist ψ) :=
  (inferInstance : Stacks.Ample.IsInvertibleModule Z (pullTwist ψ))

/-- The pulled-back coordinates `ψ^* T₀, …, ψ^* T_N`. -/
private noncomputable def pullSystem : Fin (N + 1) → Γ(pullTwist ψ, ⊤) :=
  fun i => pullbackGlobalSections ψ (twistOne k N) (coordSection i)

/-- `∑ᵢ cᵢ ψ^* Tᵢ = ψ^* (∑ᵢ cᵢ Tᵢ)`. -/
private theorem systemSection_pullSystem [ψ.IsOver (Spec (.of k))] (c : Fin (N + 1) → k) :
    systemSection (pullSystem ψ) c =
      pullbackGlobalSections ψ (twistOne k N) (formSection (linearForm c)) := by
  rw [systemSection_apply, ← sum_smul_coordSection, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackGlobalSections_smul_scalar
    k ψ _ (by simp) (c i) _).symm

/-- **The zero scheme of `∑ᵢ cᵢ ψ^* Tᵢ` is the hyperplane section `ψ⁻¹(V(∑ᵢ cᵢ Tᵢ))`.** -/
private theorem zeroScheme_pullSystem [ψ.IsOver (Spec (.of k))] (c : Fin (N + 1) → k) :
    zeroScheme Z (pullTwist ψ) (systemSection (pullSystem ψ) c) = hyperplaneSection ψ c := by
  rw [systemSection_pullSystem]
  exact Stacks.Divisors.zeroScheme_pullback ψ (twistOne k N) (formSection (linearForm c))

omit [Z.Over (Spec (.of k))] in
/-- A point lies on the hyperplane section of `c` iff the homogeneous prime of its image contains
the linear form of `c`. -/
private theorem mem_support_hyperplaneSection_iff (c : Fin (N + 1) → k) (z : Z) :
    z ∈ (hyperplaneSection ψ c).support ↔
      (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈ (ψ z).asHomogeneousIdeal := by
  rw [hyperplaneSection, Scheme.IdealSheafData.support_comap]
  exact MMP.ProjectiveSpace.mem_support_hyperplane_iff _ _

omit [Z.Over (Spec (.of k))] in
/-- The hyperplane section of a composite is the inverse image of the hyperplane section. -/
private theorem hyperplaneSection_comp {Z' : Scheme.{u}} (g : Z' ⟶ Z) (c : Fin (N + 1) → k) :
    hyperplaneSection (g ≫ ψ) c = (hyperplaneSection ψ c).comap g := by
  simp only [hyperplaneSection, Scheme.IdealSheafData.comap_comp]

/-- The linear form of a standard basis vector is the coordinate. -/
private theorem coe_linearForm_single (i : Fin (N + 1)) :
    (linearForm (Pi.single i 1 : Fin (N + 1) → k) : MvPolynomial (Fin (N + 1)) k) =
      MvPolynomial.X i := by
  classical
  simp [linearForm, Pi.single_apply]

/-- **The pulled-back coordinates generate `ψ^* 𝒪(1)`.** -/
private theorem iSup_nonvanishingOpen_pullSystem [ψ.IsOver (Spec (.of k))] :
    ⨆ c : Fin (N + 1) → k, nonvanishingOpen Z (pullTwist ψ) (systemSection (pullSystem ψ) c) =
      ⊤ := by
  refine eq_top_iff.mpr fun z _ => Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := MMP.ProjectiveSpace.exists_X_notMem (ψ z)
  refine ⟨Pi.single i 1, mem_nonvanishingOpen_of_notMem_support_zeroScheme _ _ fun h => hi ?_⟩
  rw [← coe_linearForm_single (k := k), ← mem_support_hyperplaneSection_iff, ←
    zeroScheme_pullSystem]
  exact h

end Pullback

/-! ### A general hyperplane misses finitely many given points -/

section Avoid

variable {k : Type u} [Field k] {N : ℕ}

/-- `∑ᵢ cᵢ Tᵢ`, as a polynomial, is linear in `c`. -/
private theorem coe_linearForm (c : Fin (N + 1) → k) :
    (linearForm c : MvPolynomial (Fin (N + 1)) k) =
      Fintype.linearCombination k (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))
        c := by
  simp [linearForm, Fintype.linearCombination_apply]

/-- **The hyperplanes through a point form a proper linear subspace** of the dual space: there is
a nonzero linear polynomial `Q` in the coefficients such that `∑ᵢ cᵢ Tᵢ` does not vanish at `p`
as soon as `Q(c) ≠ 0`. -/
private theorem exists_isHomogeneous_notMem (p : AlgebraicGeometry.Proj (polyGrading k N)) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q.IsHomogeneous 1 ∧ Q ≠ 0 ∧
      ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 →
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉ p.asHomogeneousIdeal := by
  classical
  set ℓ := Fintype.linearCombination k
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) with hℓ
  set K : Submodule k (Fin (N + 1) → k) :=
    (p.asHomogeneousIdeal.toIdeal.restrictScalars k).comap ℓ with hK
  obtain ⟨i, hi⟩ := MMP.ProjectiveSpace.exists_X_notMem p
  have hKtop : K < ⊤ := lt_top_iff_ne_top.mpr fun h => hi <| by
    have hmem : (Pi.single i 1 : Fin (N + 1) → k) ∈ K := h ▸ Submodule.mem_top
    rwa [hK, Submodule.mem_comap, hℓ, ← coe_linearForm, coe_linearForm_single] at hmem
  obtain ⟨g, hg0, hKg⟩ := Submodule.exists_le_ker_of_lt_top K hKtop
  set Q : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (g (Pi.single j 1)) * MvPolynomial.X j with hQ
  have heval : ∀ c, MvPolynomial.eval c Q = g c := by
    intro c
    conv_rhs => rw [← Finset.univ_sum_single c]
    simp only [hQ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
      (MvPolynomial.isHomogeneous_C_mul_X _ j)
  · intro h0
    apply hg0
    refine LinearMap.ext fun c => ?_
    rw [← heval, h0, map_zero, LinearMap.zero_apply]
  · intro c hc hmem
    apply hc
    have hcK : c ∈ K := by
      change ℓ c ∈ p.asHomogeneousIdeal.toIdeal
      rw [← coe_linearForm]
      exact hmem
    rw [heval]
    exact hKg hcK

/-- **A general hyperplane misses finitely many given points**: there is a dense open of the dual
projective space such that the hyperplane `[c]` of each of its points passes through none of
them. -/
private theorem exists_dense_open_forall_notMem (P : Set (AlgebraicGeometry.Proj (polyGrading k N)))
    (hP : P.Finite) :
    ∃ U : (AlgebraicGeometry.Proj (polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U → ∀ p ∈ P,
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉ p.asHomogeneousIdeal := by
  classical
  choose Q hQh hQ0 hQ using fun p : AlgebraicGeometry.Proj (polyGrading k N) =>
    exists_isHomogeneous_notMem p
  set R := ∏ p ∈ hP.toFinset, Q p with hR
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hQ0 p
  have hRh : R.IsHomogeneous (∑ p ∈ hP.toFinset, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun p _ => hQh p
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) R,
    dense_projectiveSpace_basicOpen hR0, fun c hc hmem p hp => hQ p c ?_⟩
  have hRc : MvPolynomial.eval c R ≠ 0 := by
    intro h0
    change R ∉ (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
    exact hmem (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨_, hRh⟩
      ((RingHom.mem_ker).mpr h0))
  rw [hR, map_prod] at hRc
  exact Finset.prod_ne_zero_iff.mp hRc p (hP.mem_toFinset.mpr hp)

end Avoid

/-! ### Finitely many points to avoid -/

section Topology

variable {Y : Type*} [TopologicalSpace Y]

/-- An irreducible set contained in `T` is irreducible as a subset of the subspace `T`. -/
private theorem isIrreducible_preimage_val {T C : Set Y} (hCT : C ⊆ T) (hC : IsIrreducible C) :
    IsIrreducible (((↑) : T → Y) ⁻¹' C) := by
  refine ⟨?_, fun u v hu hv ⟨x, hxC, hxu⟩ ⟨y, hyC, hyv⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := hC.nonempty
    exact ⟨⟨c, hCT hc⟩, hc⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨z, hzC, hzu, hzv⟩ := hC.2 u' v' hu' hv' ⟨x, hxC, hxu⟩ ⟨y, hyC, hyv⟩
  exact ⟨⟨z, hCT hzC⟩, hzC, hzu, hzv⟩

/-- **A subset of a Noetherian space has finitely many maximal irreducible subsets**: they are
the irreducible components of the subset. -/
private theorem finite_setOf_maximal_isIrreducible [NoetherianSpace Y] (T : Set Y) :
    {C : Set Y | Maximal (fun Z : Set Y => Z ⊆ T ∧ IsIrreducible Z) C}.Finite := by
  refine ((NoetherianSpace.finite_irreducibleComponents (α := T)).image
    (fun D : Set T => ((↑) : T → Y) '' D)).subset ?_
  intro C hC
  refine ⟨((↑) : T → Y) ⁻¹' C, ⟨isIrreducible_preimage_val hC.1.1 hC.1.2, fun D hD hle => ?_⟩, ?_⟩
  · have hD' := hC.2 ⟨Subtype.coe_image_subset _ _, hD.image _ continuous_subtype_val.continuousOn⟩
      (fun x hx => ⟨⟨x, hC.1.1 hx⟩, hle hx, rfl⟩)
    exact fun x hx => hD' ⟨x, hx, rfl⟩
  · change ((↑) : T → Y) '' (((↑) : T → Y) ⁻¹' C) = C
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hC.1.1]

/-- **A Noetherian quasi-sober `T₀` space has a finite dense subset**: the generic points of its
irreducible components. -/
private theorem exists_finite_dense [NoetherianSpace Y] [QuasiSober Y] [T0Space Y] :
    ∃ E : Set Y, E.Finite ∧ Dense E := by
  refine ⟨⋃ Z ∈ irreducibleComponents Y, {e | IsGenericPoint e Z},
    NoetherianSpace.finite_irreducibleComponents.biUnion fun Z _ =>
      Set.Subsingleton.finite fun a ha b hb => IsGenericPoint.eq ha hb,
    dense_iff_inter_open.2 ?_⟩
  rintro V hV ⟨y, hy⟩
  obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
    isIrreducible_singleton
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨e, he⟩ := QuasiSober.sober hZ.1 hZc
  exact ⟨e, (he.specializes (hyZ rfl)).mem_open hV hy, Set.mem_biUnion hZ he⟩

/-- **Finitely many points detect the maximal irreducible subsets** of a subset `T` of a Noetherian
quasi-sober `T₀` space: the generic points of their closures. -/
private theorem exists_finite_isGenericPoint [NoetherianSpace Y] [QuasiSober Y] [T0Space Y]
    (T : Set Y) :
    ∃ G : Set Y, G.Finite ∧ ∀ C : Set Y, Maximal (fun Z : Set Y => Z ⊆ T ∧ IsIrreducible Z) C →
      ∃ e ∈ G, IsGenericPoint e (closure C) := by
  refine ⟨⋃ C ∈ {C : Set Y | Maximal (fun Z : Set Y => Z ⊆ T ∧ IsIrreducible Z) C},
    {e | IsGenericPoint e (closure C)},
    (finite_setOf_maximal_isIrreducible T).biUnion fun C _ =>
      Set.Subsingleton.finite fun a ha b hb => IsGenericPoint.eq ha hb, fun C hC => ?_⟩
  obtain ⟨e, he⟩ := QuasiSober.sober hC.1.2.closure isClosed_closure
  exact ⟨e, Set.mem_biUnion hC he, he⟩

end Topology

/-! ### General normality -/

/-- **A general hyperplane section of a normal variety is normal**: Bertini for the free system of
pulled-back coordinates. -/
private theorem exists_dense_open_isNormal_hyperplaneSection {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsVariety k (X ↘ Spec (.of k))] (φ : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [φ.IsOver (Spec (.of k))] :
    ∃ U : (AlgebraicGeometry.Proj (polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        IsNormal X → IsNormal (hyperplaneSection φ c).subscheme := by
  by_cases hX : IsNormal X
  · obtain ⟨U, hU, h⟩ := (exists_dense_open_isNormal_zeroScheme (k := k) (X := X)
      (pullSystem φ) (iSup_nonvanishingOpen_pullSystem φ)).2
    exact ⟨U, hU, fun c hc hmem _ => zeroScheme_pullSystem φ c ▸ h c hc hmem⟩
  · exact ⟨⊤, by simpa using dense_univ, fun _ _ _ h => absurd h hX⟩

/-- **Bertini for general hyperplane sections.** Let `k` be algebraically closed of
characteristic zero, `φ : X ⟶ ℙᴺ_k` a `k`-immersion of a variety, `f : W ⟶ X` a `k`-morphism
from a smooth variety, `j a : S a ⟶ W` (`a ∈ A`, `A` finite) immersions with `S a` smooth over
`k`, and `T i ⊆ X` (`i ∈ J`, `J` finite) subsets. There is a dense open `U` of the dual
projective space such that for every hyperplane `[c] ∈ U` the hyperplane section
`X_H = hyperplaneSection φ c` is normal if `X` is normal, its pullback `f⁻¹(X_H)` is smooth over
`k`, every trace `f⁻¹(X_H) ∩ S a` is smooth over `k` and nowhere dense in `S a`, and no
irreducible component of any `T i` (a maximal irreducible subset of `T i`) is contained in
`X_H`. -/
@[mmp "lem_mmp_foundation_oai_stratified_hyperplane_bertini"]
theorem exists_dense_open_hyperplaneSection_stratified {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsVariety k (X ↘ Spec (.of k))]
    (φ : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsImmersion φ]
    (hφ : φ ≫ projToSpecCoeff k N = X ↘ Spec (.of k))
    {W : Scheme.{u}} [W.Over (Spec (.of k))] [IsVariety k (W ↘ Spec (.of k))]
    [Smooth (W ↘ Spec (.of k))] (f : W ⟶ X) [f.IsOver (Spec (.of k))]
    {A : Type u} [Finite A] {S : A → Scheme.{u}} (j : (a : A) → S a ⟶ W)
    [∀ a, IsImmersion (j a)] [∀ a, Smooth (j a ≫ W ↘ Spec (.of k))]
    {J : Type u} [Finite J] (T : J → Set X) :
    ∃ U : (AlgebraicGeometry.Proj (polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        (IsNormal X → IsNormal (hyperplaneSection φ c).subscheme) ∧
        Smooth (((hyperplaneSection φ c).comap f).subschemeι ≫ W ↘ Spec (.of k)) ∧
        (∀ a, Smooth ((((hyperplaneSection φ c).comap f).comap (j a)).subschemeι ≫ j a ≫
            W ↘ Spec (.of k)) ∧
          interior ((((hyperplaneSection φ c).comap f).comap (j a)).support : Set (S a)) = ∅) ∧
        ∀ (i : J) (C : Set X), Maximal (fun Z : Set X => Z ⊆ T i ∧ IsIrreducible Z) C →
          ¬ C ⊆ ((hyperplaneSection φ c).support : Set X) := by
  classical
  haveI : φ.IsOver (Spec (.of k)) := ⟨hφ⟩
  obtain ⟨U₁, hU₁, hN⟩ := exists_dense_open_isNormal_hyperplaneSection φ
  obtain ⟨U₂, hU₂, hS⟩ := (exists_dense_open_smooth_zeroScheme (k := k) (X := W)
    (pullSystem (f ≫ φ)) (iSup_nonvanishingOpen_pullSystem (f ≫ φ)) j).2
  have : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)),
      __ := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have : IsNoetherian W :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of k)),
      __ := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of k)) }
  have (a : A) : NoetherianSpace (S a) :=
    (IsPreimmersion.isEmbedding (j a)).isInducing.noetherianSpace
  choose E hEfin hE using fun a => exists_finite_dense (Y := S a)
  choose G hGfin hG using fun i => exists_finite_isGenericPoint (Y := X) (T i)
  obtain ⟨U₃, hU₃, hA⟩ := exists_dense_open_forall_notMem
    ((⋃ a, (fun e => φ (f (j a e))) '' E a) ∪ ⋃ i, φ '' G i)
    ((Set.finite_iUnion fun a => (hEfin a).image _).union
      (Set.finite_iUnion fun i => (hGfin i).image _))
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, ?_, fun c hc hmem => ?_⟩
  · simp only [Opens.coe_inf]
    exact (hU₁.inter_of_isOpen_left hU₂ U₁.isOpen).inter_of_isOpen_left hU₃
      (U₁.isOpen.inter U₂.isOpen)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hmem
  have hS' := hS c hc h2
  rw [zeroScheme_pullSystem, hyperplaneSection_comp] at hS'
  refine ⟨hN c hc h1, hS'.1 inferInstance, fun a => ⟨hS'.2 a, ?_⟩, fun i C hC hCsub => ?_⟩
  · rw [← hyperplaneSection_comp, ← hyperplaneSection_comp]
    exact interior_eq_empty_iff_dense_compl.2 <| (hE a).mono fun e he h =>
      hA c hc h3 _ (Or.inl (Set.mem_iUnion.mpr ⟨a, e, he, rfl⟩))
        ((mem_support_hyperplaneSection_iff _ c e).mp h)
  · obtain ⟨e, he, hgen⟩ := hG i C hC
    exact hA c hc h3 _ (Or.inr (Set.mem_iUnion.mpr ⟨i, e, he, rfl⟩))
      ((mem_support_hyperplaneSection_iff φ c e).mp
        (closure_minimal hCsub (hyperplaneSection φ c).support.isClosed hgen.mem))

end Bertini

end MMP.Threefold.Bridges

namespace MMP

/-! ### Fibres of a restriction -/

/-- A property respecting isomorphisms passes along a commutative square whose horizontal
edges are isomorphisms. -/
private lemma of_isPullback_of_isIso {C : Type*} [Category C] {P : MorphismProperty C}
    [P.RespectsIso] {A B Y Z : C} {a : A ⟶ B} {p : A ⟶ Y} {q : B ⟶ Z} {e : Y ⟶ Z}
    (hsq : IsPullback a p q e) [IsIso e] (h : P p) : P q :=
  have := hsq.isIso_fst_of_isIso
  (P.arrow_mk_iso_iff (Arrow.isoMk (asIso a) (asIso e) hsq.w)).1 h

/-- The fibre of `f` at the image of `u` is a base change of the fibre of `f ∣_ U` at `u`, the
residue fields being isomorphic. -/
private lemma fiber_of_restrict {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (u : U.toScheme)
    (h : P ((f ∣_ U).fiberToSpecResidueField u)) :
    P (f.fiberToSpecResidueField (U.ι u)) :=
  of_isPullback_of_isIso
    (isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f U).flip u) h

/-- A nonempty proper scheme over a field has finite Krull dimension. -/
private lemma exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of k)) [IsProper π] [Nonempty Y] : ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 <|
    Order.krullDim_ne_bot_iff (α := TopologicalSpace.IrreducibleCloseds Y) |>.2
      ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  lift d to ℕ using by rintro rfl; exact topologicalKrullDim_ne_top_of_isProper k π hd.symm
  exact ⟨d, hd.symm⟩

/-! ### Geometrically integral generic fibres -/

/-- If `P` holds for `f ∣_ U`, it holds for the fibre of `f` over every point of `U`. -/
private lemma fiber_of_morphismRestrict {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (h : P (f ∣_ U))
    {y : Y} (hy : y ∈ U) : P (f.fiberToSpecResidueField y) :=
  fiber_of_restrict (P := P) f U ⟨y, hy⟩ (P.pullback_snd _ _ h)

/-- **Geometrically integral proper generic fibres spread.** Let `f : X ⟶ Spec R` be proper,
where `R` is a domain of finite type over a field `k₀` of characteristic zero. If the generic
fibre of `f` is geometrically integral, there is a nonzero `r : R` such that over `D(r)` every
fibre of `f` is geometrically integral and has the dimension of the generic fibre. -/
@[mmp "thm_mmp_proper_generic_integral_fibres"]
theorem exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic
    (k₀ : Type u) [Field k₀] [CharZero k₀]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k₀ R] [Algebra.FiniteType k₀ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hgi : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R))))) :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal →
      GeometricallyIntegral (f.fiberToSpecResidueField s) ∧
      topologicalKrullDim (f.fiber s) =
        topologicalKrullDim (f.fiber (genericPoint (Spec (CommRingCat.of R)))) := by
  set η := genericPoint (Spec (CommRingCat.of R))
  have hη : IsGenericPoint η Set.univ := genericPoint_spec _
  obtain ⟨V₁, hV₁, hirr⟩ := geometricallyIrreducibleAfterShrinking f inferInstance inferInstance
    inferInstance η hη inferInstance
  obtain ⟨V₂, hV₂, hred⟩ :=
    exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType f η hη
  have : IsIntegral (f.fiber η) := self_of_isIntegral_of_geometrically hgi.geometrically_isIntegral
  have hprop : IsProper (f.fiberToSpecResidueField η) :=
    inferInstanceAs (IsProper (pullback.snd f _))
  obtain ⟨n, hn⟩ := @exists_topologicalKrullDim_eq_natCast _ _ _ _ hprop _
  obtain ⟨V₃, hV₃, hdim⟩ := exists_nonempty_open_fiberDimension_eq f n η hη hn
  have hV : ((V₁ : Set (Spec (CommRingCat.of R))) ∩ V₂ ∩ V₃).Nonempty :=
    nonempty_preirreducible_inter (V₁.isOpen.inter V₂.isOpen) V₃.isOpen
      (nonempty_preirreducible_inter V₁.isOpen V₂.isOpen (Set.nonempty_coe_sort.1 hV₁)
        (Set.nonempty_coe_sort.1 hV₂)) hV₃
  obtain ⟨r, hr, hrV⟩ := MMP.Threefold.Bridges.exists_ne_zero_forall_mem_of_isOpen
    (R := R) _ ((V₁.isOpen.inter V₂.isOpen).inter V₃.isOpen) hV
  refine ⟨r, hr, fun s hs => ?_⟩
  obtain ⟨⟨hs₁, hs₂⟩, hs₃⟩ := hrV s hs
  have := fiber_of_morphismRestrict (P := @GeometricallyIrreducible) f V₁ hirr hs₁
  have := fiber_of_morphismRestrict (P := @GeometricallyReduced) f V₂ hred hs₂
  exact ⟨.of_geometricallyReduced_of_geometricallyIrreducible _, (hdim s hs₃).trans hn.symm⟩

/-! ### Normal geometrically integral generic fibres -/

/-- **Proper normal generic fibres spread geometric integrality.** Let `f : X ⟶ Spec R` be
proper, where `R` is a domain of finite type over a field `k₀` of characteristic zero. If the
generic fibre of `f` is geometrically integral and normal, there is a nonzero `r : R` such that
over `D(r)` every fibre of `f` is geometrically integral and geometrically normal and has the
dimension of the generic fibre. -/
@[mmp "lem_mmp_proper_normal_generic_integrality"]
theorem exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper
    (k₀ : Type u) [Field k₀] [CharZero k₀]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k₀ R] [Algebra.FiniteType k₀ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hgi : GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))))
    (hF : IsNormal (f.fiber (genericPoint (Spec (CommRingCat.of R))))) :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal →
      GeometricallyIntegral (f.fiberToSpecResidueField s) ∧
      geometrically IsNormal (f.fiberToSpecResidueField s) ∧
      topologicalKrullDim (f.fiber s) =
        topologicalKrullDim (f.fiber (genericPoint (Spec (CommRingCat.of R)))) := by
  obtain ⟨r₁, hr₁, hnorm⟩ := exists_ne_zero_forall_geometrically_isNormal_fiber k₀ f hF
  obtain ⟨r₂, hr₂, hint⟩ :=
    exists_ne_zero_forall_geometricallyIntegral_fiber_of_isProper_of_generic k₀ f hgi
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun s hs => ?_⟩
  obtain ⟨hgis, hdim⟩ := hint s fun h => hs (s.asIdeal.mul_mem_left _ h)
  exact ⟨hgis, (hnorm s fun h => hs (s.asIdeal.mul_mem_right _ h)).1, hdim⟩

end MMP

end
