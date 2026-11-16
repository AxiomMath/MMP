module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
import MMP.AlgebraicGeometry.Intersection.ThreefoldEffectiveIntersection
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Free pencils of numerical dimension one, and log resolutions adapted to a procedure datum

Two results of *Flips and abundance for algebraic threefolds*.

* FA 15.13. Let `(X, Δ_X)` satisfy the assumptions of FA 15.4 and `L = K_X + Δ_X`. If the
  numerical dimension `ν(X, L)` is at most one, then `L` is eventually free and composed of a
  pencil. Writing `|mL| = F + |M|` with fixed part `F`, two general members of `|M|` are disjoint
  and a general member misses `Supp F`, by the vanishing of `L² · H`; the Stein factorization
  `p : X ⟶ C` of the pencil has `M ∼ p^* B` with `B` ample on the curve `C`, Zariski's lemma makes
  `F` a pull-back from `C`, and so `L ∼_ℚ p^* N` with `N` ample on `C`.
* FA 18.12.2. Let `f : X ⟶ Z` be a small projective contraction of a normal variety with a
  boundary `D`, and `(π, (F_j), H')` a procedure datum for `(X, D, f)` with `H = f^*H'`. Over
  `Z ∖ Supp H'` the morphism `f` is an isomorphism and the pair is snc, so a projective log
  resolution of `(X, D + Supp H)` which is an isomorphism over the snc locus makes `g ≫ f` an
  isomorphism over `Z ∖ Supp H'`.

## Main results

* `MMP.Mori.linearSystemLocus_eq_top_of_forall`: if every point lies in the nonvanishing locus of
  a global section of `ℒ`, the linear system of any basis of `H⁰(X, ℒ)` is defined on all of `X`.
* `MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor`: for `M` Cartier, a nonzero
  section `σ` of `𝒪_X(M)` vanishes exactly on `Supp (σ)₀`.
* `MMP.Mori.Divisor.IsBasepointFree.linearSystemLocus_eq_top`: a basepoint free `|M|` gives the
  open `linearSystemLocus = X` for every basis of `H⁰(X, 𝒪_X(M))`.
* `MMP.Flips.SatisfiesAbundanceAssumptions.isEventuallyFreePencil_of_numericalDimension_le_one`:
  FA 15.13, `ν(X, K_X + Δ_X) ≤ 1` gives an eventually free pencil.
* `MMP.Flips.ProcedureDatum.exists_isLogResolution_isIso_restrict`: FA 18.12.2, a projective log
  resolution of `(X, D ⊔ Supp H)` with `g ≫ f` an isomorphism over `Z ∖ Supp H'`.

## Implementation notes

A log resolution is `MMP.Flips.IsLogResolution`, which only depends on the support of the
divisor it resolves, but asks the divisor to be a boundary. Since `⌊D⌋ ⊆ Supp H`
(condition 18.12.1.5), the sum `D + Supp H` has coefficient `2` along the components of `⌊D⌋`;
the pair `(X, D + Supp H)` is therefore taken with the boundary `D ⊔ Supp H`, which has the same
support. The source works over `ℂ`; both statements are made over a field of characteristic
zero (algebraically closed for FA 15.13). The auxiliary lemmas of each proof live in the
namespaces `Proof_lem_fa15_nu_one_free_pencil` and
`Proof_lem_fa18_procedure_log_resolution_exists`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.13 and
  18.12.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

universe v

/-! ### Linear systems without base points -/

section LinearSystemLocus

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- If every point of `X` lies in the nonvanishing locus of some global section of `ℒ`, then the
open of the linear system of any basis of `H⁰(X, ℒ)` is all of `X`. -/
theorem linearSystemLocus_eq_top_of_forall (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤))
    (h : ∀ x : X, ∃ s : Γ(L, ⊤), x ∈ Stacks.Ample.nonvanishingLocus L s) :
    linearSystemLocus k L b = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [mem_linearSystemLocus_iff]
  by_contra hx
  push Not at hx
  obtain ⟨s, hs⟩ := h x
  let V : Submodule k Γ(L, ⊤) :=
    { carrier := {t | x ∉ Stacks.Ample.nonvanishingLocus L t}
      add_mem' := fun ha hb hab => (Stacks.Ample.nonvanishingLocus_add_subset L _ _ hab).elim ha hb
      zero_mem' := by simp
      smul_mem' := fun c t ht hct => ht (Stacks.Ample.nonvanishingLocus_smul_subset L
        (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X c) t hct) }
  have hV : (⊤ : Submodule k Γ(L, ⊤)) ≤ V := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  exact (hV (Submodule.mem_top (x := s))) hs

end LinearSystemLocus

namespace Divisor

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-! ### Sections and their divisors of zeros -/

section ZeroDivisor

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- A nonzero section `σ` of `𝒪_X(M)` is the rational function `φ` with `div φ + M = (σ)₀`;
multiplication by `φ⁻¹` carries it to the section `1` of `𝒪_X((σ)₀)`. -/
private theorem divisorialSheafMulIso_app_eq_oneSection {M : Divisor X}
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    ((Divisor.divisorialSheafMulIso (D := M) (D' := M.zeroDivisor σ hσ)
        (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
          rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
            PrimeDivisor.ord_inv]
          ring).hom.app ⊤ σ) =
      MMP.Threefold.Mori.oneSection (M.zeroDivisor_nonneg σ hσ) := by
  refine Subtype.ext (funext fun Z => ?_)
  change ((Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ : (RationalFunctions X)ˣ).1 Z.1 *
      σ.1 Z = ((Divisor.structureSheafToDivisorialSheaf _).app ⊤ (1 : Γ(X, ⊤))).1 Z
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
  have h1 : σ.1 Z = ((Divisor.isUnit_sectionToRationalFunctions hσ).unit :
      RationalFunctions X) Z.1 := rfl
  rw [h1, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rfl

/-- **The nonvanishing locus of a section is the complement of its divisor of zeros**, for a
Cartier divisor `M`. -/
theorem nonvanishingLocus_eq_compl_supp_zeroDivisor {M : Divisor X} (hM : M.IsCartier)
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    haveI := hM.isInvertibleModule_divisorialSheaf
    Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ = ((M.zeroDivisor σ hσ).supp : Set X)ᶜ := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  haveI := hZc.isInvertibleModule_divisorialSheaf
  rw [← Stacks.CokernelSupport.nonvanishingLocus_iso_app (Divisor.divisorialSheafMulIso (D := M)
    (D' := M.zeroDivisor σ hσ) (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
      rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
        PrimeDivisor.ord_inv]
      ring) σ]
  rw [divisorialSheafMulIso_app_eq_oneSection σ hσ]
  exact MMP.Threefold.Mori.nonvanishingLocus_oneSection _ hZc

/-- **The linear system of a basepoint free Cartier divisor is defined on all of `X`.** If `M`
is Cartier and `|M|` is basepoint free, then for every basis `b` of `H⁰(X, 𝒪_X(M))` the open
`linearSystemLocus` is all of `X`. -/
theorem IsBasepointFree.linearSystemLocus_eq_top (k : Type v) [Field k] [X.Over (Spec (.of k))]
    {M : Divisor X} (hM : M.IsCartier) (hbpf : M.IsBasepointFree) {ι : Type v}
    (b : Module.Basis ι k Γ(M.divisorialSheaf, ⊤)) :
    haveI := hM.isInvertibleModule_divisorialSheaf
    linearSystemLocus k M.divisorialSheaf b = ⊤ := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  refine linearSystemLocus_eq_top_of_forall k _ b fun x => ?_
  have hx : x ∉ (M.baseLocus : Set X) := by
    rw [hbpf]
    exact id
  rw [mem_baseLocus_iff] at hx
  push Not at hx
  obtain ⟨σ, hσ, hxσ⟩ := hx
  exact ⟨σ, by rwa [nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ hσ]⟩

end ZeroDivisor

end Divisor

end MMP.Mori

namespace Proof_lem_fa15_nu_one_free_pencil

open MMP.Mori MMP.Flips

universe v

/-! ### Linear systems on a curve -/

section Curve

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

/-- Dimension of the closure of the range of a map. -/
private noncomputable def rdim {A B : Type*} [TopologicalSpace B] (f : A → B) : WithBot ℕ∞ :=
  topologicalKrullDim (closure (Set.range f))

private theorem rdim_comp_surjective {A A' B : Type*} [TopologicalSpace B] (f : A → B)
    {h : A' → A} (hh : Function.Surjective h) : rdim (f ∘ h) = rdim f := by
  unfold rdim
  rw [hh.range_comp]

private theorem rdim_homeomorph_comp {A B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (e : B ≃ₜ C) : rdim (e ∘ f) = rdim f := by
  unfold rdim
  rw [Set.range_comp, ← e.image_closure]
  exact ((e.image _).isHomeomorph.topologicalKrullDim_eq).symm

/-- The global sections of an invertible sheaf on a proper `k`-scheme are finite-dimensional. -/
private theorem finiteDimensional_globalSections (k : Type v) [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsLocallyNoetherian X] (F : X.Modules)
    [Stacks.Ample.IsInvertibleModule X F] :
    letI : X.Over (Spec (.of k)) := ⟨sX⟩
    letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k X F
    FiniteDimensional k Γ(F, ⊤) := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    ‹Stacks.Ample.IsInvertibleModule X F›
  have : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X F
  have := finiteDimensional_cohomologyOverField_of_isProper k sX F 0
  have e := (cohomologyOverFieldZeroLinearIso k sX F).toLinearEquiv
  have hEq : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  have key : ∀ φ : k →+* Γ(X, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(F, ⊤) φ; FiniteDimensional k Γ(F, ⊤)) := by
    rintro φ rfl
    -- elaborated before the goal's `letI` instance is in scope
    have h := Module.Finite.equiv e
    exact h
  refine key _ ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ sX.appTop).hom = _
  rw [hEq]

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

private theorem topologicalKrullDim_linearSystemImage (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) :
    topologicalKrullDim (linearSystemImage k L b) = rdim (linearSystemMap k L b).base := by
  have hemb := (linearSystemImageIdeal k L b).subschemeι.isClosedEmbedding.isEmbedding
  rw [hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq, rdim]
  have : Set.range (linearSystemImageIdeal k L b).subschemeι.base =
      closure (Set.range (linearSystemMap k L b).base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, linearSystemImageIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [this]

open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare in
private theorem linearSystemMap_comp_basisIso (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (e : Fin (n + 1) ≃ ι)
    (hgen : GeneratesStalks (fun i => b (e i))) :
    linearSystemMap k L b ≫
        (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
          ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm)).hom.left =
      (linearSystemLocus k L b).ι ≫
        toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k)) := by
  rw [linearSystemMap, morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso]
  refine CategoryTheory.Limits.pullback.hom_ext ?_ ?_
  · rw [toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst]
    rfl
  · rw [toProjectiveSpaceOver_snd, Category.assoc, toProjectiveSpaceOver_snd,
      comp_toProjectiveSpaceAtUniverse _ _ _
        (pullbackTuple (linearSystemLocus k L b).ι ⟨L, ‹_›, _, hgen⟩).generates]
    congr 1
    funext i
    simp [Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.basisSections,
      linearSystemRestrict]
    rfl

private theorem topologicalKrullDim_linearSystemImage_eq (k : Type v) [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type v}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (e : Fin (n + 1) ≃ ι)
    (hgen : GeneratesStalks (fun i => b (e i))) (htop : linearSystemLocus k L b = ⊤) :
    topologicalKrullDim (linearSystemImage k L b) =
      rdim (toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k))).base := by
  rw [topologicalKrullDim_linearSystemImage]
  let E := (Over.forget _).mapIso (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
    ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm))
  refine (rdim_homeomorph_comp _ (Scheme.homeoOfIso E)).symm.trans ?_
  have h1 : ⇑(Scheme.homeoOfIso E) ∘ ⇑(linearSystemMap k L b).base =
      ⇑(linearSystemMap k L b ≫ E.hom).base := rfl
  have hE : E.hom = (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso
    ((Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm)).hom.left := rfl
  rw [h1, hE, linearSystemMap_comp_basisIso k L b e hgen]
  refine rdim_comp_surjective
    (⇑(toProjectiveSpaceOver (fun i => b (e i)) hgen (X ↘ Spec (.of k))).base)
    (h := ⇑(linearSystemLocus k L b).ι.base) ?_
  rw [← Set.range_eq_univ, Scheme.Opens.range_ι, htop]
  rfl

private theorem generatesStalks_of_linearSystemLocus_eq_top (k : Type v) [Field k]
    {X : Scheme.{v}} [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {ι : Type v} (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ}
    (e : Fin (n + 1) ≃ ι) (htop : linearSystemLocus k L b = ⊤) :
    GeneratesStalks (fun i => b (e i)) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
    obtain ⟨j, hj⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
    exact ⟨e.symm j, show x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L (b (e (e.symm j))) by
      rw [Equiv.apply_symm_apply]; exact hj⟩

/-- A basis of the sections of an invertible sheaf on a nonempty scheme with `U = X` is indexed by
a type equivalent to some `Fin (n + 1)`, when the sections are finite-dimensional. -/
private theorem exists_equiv_fin_of_linearSystemLocus_eq_top (k : Type v) [Field k]
    {X : Scheme.{v}} [Nonempty X] [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {ι : Type v} (b : Module.Basis ι k Γ(L, ⊤))
    [FiniteDimensional k Γ(L, ⊤)] (htop : linearSystemLocus k L b = ⊤) :
    ∃ n : ℕ, Nonempty (Fin (n + 1) ≃ ι) := by
  haveI : Finite ι := Module.Finite.finite_basis b
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j, -⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
  cases m with
  | zero => exact (e j).elim0
  | succ n => exact ⟨n, ⟨e.symm⟩⟩

/-- The range of a closed map has dimension at most that of its source. -/
private theorem topologicalKrullDim_range_le_of_isClosedMap {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [QuasiSober B] [T0Space B] (f : A → B) (hf : Continuous f)
    (hc : IsClosedMap f) :
    topologicalKrullDim (Set.range f) ≤ topologicalKrullDim A := by
  have : QuasiSober (Set.range f) := hc.isClosed_range.isClosedEmbedding_subtypeVal.quasiSober
  refine Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    (Set.rangeFactorization f) (hf.subtype_mk _) Set.rangeFactorization_surjective (Or.inl ?_)
  intro a y hy
  have hy' : f a ⤳ y.1 := hy.map continuous_subtype_val
  obtain ⟨a', ha', hfa'⟩ := hc.specializingMap hy'
  exact ⟨a', ha', Subtype.ext hfa'⟩

/-- An irreducible sober space of dimension at most zero is a point. -/
private theorem subsingleton_of_topologicalKrullDim_le_zero {S : Type*} [TopologicalSpace S]
    [IrreducibleSpace S] [QuasiSober S] [T0Space S] (h : topologicalKrullDim S ≤ 0) :
    Subsingleton S := by
  have key : ∀ p : S, closure {p} = Set.univ := by
    intro p
    by_contra hne
    let Zp : TopologicalSpace.IrreducibleCloseds S :=
      ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩
    let Zt : TopologicalSpace.IrreducibleCloseds S :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
    have hlt : Zp < Zt := lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq =>
      hne (congrArg (fun Z : TopologicalSpace.IrreducibleCloseds S => (Z : Set S)) heq)
    exact (Order.krullDim_nonpos_iff_forall_isMax.mp h Zp).not_lt hlt
  exact ⟨fun p q => (show IsGenericPoint p Set.univ from key p).eq (key q)⟩

private theorem eq_one_of_le_one_of_not_le_zero {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) :
    d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      obtain rfl : m = 1 := by
        have : m ≤ 1 := by exact_mod_cast h1
        have : ¬ m ≤ 0 := fun h => h0 (by exact_mod_cast h)
        omega
      rfl

/-- If the image of `φ_s` is a point, some `sⱼ` vanishes nowhere. -/
private theorem exists_forall_mem_nonvanishingLocus_of_subsingleton {Z S : Scheme.{v}}
    [Nonempty Z] {n : ℕ} {L : Z.Modules} [Stacks.Ample.IsInvertibleModule Z L]
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (f : Z ⟶ S)
    (h : (Set.range (toProjectiveSpaceOver s hs f).base).Subsingleton) :
    ∃ j, ∀ z, z ∈ Stacks.Ample.nonvanishingLocus L (s j) := by
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks s hs z₀
  have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart s hs
    (toProjectiveSpaceOver s hs f) (fun i => ι_toProjectiveSpaceOver s hs f i) j
  refine ⟨j, fun z => ?_⟩
  have h0 : z₀ ∈ (toProjectiveSpaceOver s hs f) ⁻¹ᵁ projectiveSpaceOver.standardChart n S j := by
    rwa [hpre]
  have hz : z ∈ (toProjectiveSpaceOver s hs f) ⁻¹ᵁ projectiveSpaceOver.standardChart n S j := by
    rw [Scheme.Hom.mem_preimage] at h0 ⊢
    rwa [h ⟨z, rfl⟩ ⟨z₀, rfl⟩]
  rwa [hpre] at hz

private theorem isClosedMap_toProjectiveSpaceOver {Z S : Scheme.{v}} (f : Z ⟶ S) [IsProper f]
    {n : ℕ} {L : Z.Modules} [Stacks.Ample.IsInvertibleModule Z L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) : IsClosedMap (toProjectiveSpaceOver s hs f).base := by
  have : IsProper (toProjectiveSpaceOver s hs f ≫ CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} n))) := by
    rw [toProjectiveSpaceOver_fst]
    infer_instance
  have := IsProper.of_comp (toProjectiveSpaceOver s hs f) (CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} n)))
  exact (toProjectiveSpaceOver s hs f).isClosedMap

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- `𝒪_X(E)^{⊗ n} ≅ 𝒪_X(nE)` for a Cartier divisor `E`. -/
private noncomputable def tensorPowDivisorialIso {X : Scheme.{v}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (E : Divisor X) (hE : E.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] :
    (n : ℕ) → tensorPowModule X E.divisorialSheaf (n : ℤ) ≅ (n • E).divisorialSheaf
  | 0 => tensorPowModuleZeroIso X E.divisorialSheaf ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫
      eqToIso (by rw [zero_nsmul])
  | (n + 1) =>
      tensorPowModuleCongr X E.divisorialSheaf
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X E.divisorialSheaf (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowDivisorialIso E hE n)
          (tensorPowModuleOneIso X E.divisorialSheaf) ≪≫
        (hE.nsmul n).divisorialSheafTensorIso hE ≪≫
        eqToIso (by rw [succ_nsmul])

/-- **The curve part.** A `ℚ`-divisor on a normal projective curve having an ample Cartier
multiple is eventually free and composed of a pencil. -/
private theorem isEventuallyFreePencil_of_isAmple_of_curve {k : Type v} [Field k]
    [IsAlgClosed k] {C : Scheme.{v}} [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdim : topologicalKrullDim C = 1) (N : QDivisor C) (n : ℕ) (hn : 0 < n) (A : Divisor C)
    (hA : Divisor.toQDivisor A = (n : ℚ) • N) (hAc : A.IsCartier) (hAa : A.IsAmple hAc) :
    IsEventuallyFreePencil k sC N := by
  classical
  haveI := hC.toIsIntegral
  haveI : IsProper sC := isProper_of_isProjectiveMorphism sC hC.isProjective
  haveI : AlgebraicGeometry.IsVariety k sC := hC.toIsVariety
  haveI : AlgebraicGeometry.IsCurve k sC := ⟨hdim⟩
  letI : C.Over (Spec (.of k)) := ⟨sC⟩
  haveI := hAc.isInvertibleModule_divisorialSheaf
  obtain ⟨N₀, r, s, hN₀, hgen, haff⟩ :=
    Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple _ hAa
  have hEc : (N₀ • A).IsCartier := hAc.nsmul N₀
  haveI := hEc.isInvertibleModule_divisorialSheaf
  set e := tensorPowDivisorialIso A hAc N₀
  set t : Fin (r + 1) → Γ((N₀ • A).divisorialSheaf, ⊤) := fun i => e.hom.app ⊤ (s i)
  have ht : ∀ i, Stacks.Ample.nonvanishingLocus _ (t i) =
      Stacks.Ample.nonvanishingLocus _ (s i) :=
    fun i => Stacks.CokernelSupport.nonvanishingLocus_iso_app e (s i)
  refine ⟨N₀ * n, Nat.mul_pos (by omega) hn, N₀ • A, ?_, hC, hEc, ?_⟩
  · rw [map_nsmul, hA, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    rfl
  haveI := finiteDimensional_globalSections k sC (N₀ • A).divisorialSheaf
  let b := Module.Basis.ofVectorSpace k Γ((N₀ • A).divisorialSheaf, ⊤)
  have hloc : linearSystemLocus k _ b = ⊤ :=
    linearSystemLocus_eq_top_of_forall k _ b fun x => by
      obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hgen x
      exact ⟨t i, by rwa [ht]⟩
  refine ⟨_, b, hloc, ?_⟩
  obtain ⟨m, ⟨e'⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ b hloc
  have hg := generatesStalks_of_linearSystemLocus_eq_top k _ b e' hloc
  rw [topologicalKrullDim_linearSystemImage_eq k _ b e' hg hloc]
  have hφc := isClosedMap_toProjectiveSpaceOver sC (fun i => b (e' i)) hg
  unfold rdim
  change topologicalKrullDim (closure (Set.range
    (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base)) = 1
  rw [hφc.isClosed_range.closure_eq]
  refine eq_one_of_le_one_of_not_le_zero ?_ fun h0 => ?_
  · exact (topologicalKrullDim_range_le_of_isClosedMap _
      (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).continuous hφc).trans hdim.le
  haveI : QuasiSober (Set.range (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base) :=
    hφc.isClosed_range.isClosedEmbedding_subtypeVal.quasiSober
  haveI : IrreducibleSpace
      (Set.range (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).base) := by
    refine Subtype.irreducibleSpace ?_
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C).image _
      (toProjectiveSpaceOver (fun i => b (e' i)) hg sC).continuous.continuousOn
  have hsub := (Set.subsingleton_coe _).1 (subsingleton_of_topologicalKrullDim_le_zero h0)
  obtain ⟨j, hj⟩ := exists_forall_mem_nonvanishingLocus_of_subsingleton _ hg _ hsub
  -- every section is a multiple of the nowhere vanishing `b (e' j)`
  obtain ⟨x₀⟩ : Nonempty C := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_mem_nvCover_of_generatesStalks s hgen x₀
  have hle : (⊤ : C.Opens) ≤ Stacks.NonvanishingOpen.nonvanishingOpen C _ (b (e' j)) :=
    fun z _ => hj z
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul C (N₀ • A).divisorialSheaf
    (b (e' j)) hle).2 (t i₀)
  have hres : (N₀ • A).divisorialSheaf.presheaf.map
      (homOfLE (le_refl (⊤ : C.Opens))).op (b (e' j)) = b (e' j) := by
    rw [show homOfLE (le_refl (⊤ : C.Opens)) = 𝟙 ⊤ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [hres] at ha
  have hloc0 : Stacks.Ample.nonvanishingLocus _ (t i₀) = (C.basicOpen a : Set C) := by
    rw [← ha, Stacks.Ample.nonvanishingLocus_smul]
    exact Set.inter_eq_left.mpr fun z _ => hj z
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : x₀ ∈ Stacks.Ample.nonvanishingLocus _ (t i₀) := by rwa [ht]
    rwa [hloc0, Scheme.basicOpen_zero] at this
  obtain ⟨a', ha'⟩ :=
    (Stacks.Models.isField_globalSections_of_connectedSpace k sC).mul_inv_cancel ha0
  have htop : nvCover s i₀ = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    change z ∈ Stacks.Ample.nonvanishingLocus _ (s i₀)
    rw [← ht, hloc0, Scheme.basicOpen_of_isUnit _ (.of_mul_eq_one a' ha')]
    trivial
  exact IsAffineOpen.ne_top_of_isCurve k sC (haff i₀) htop

end Curve

/-! ### From a free pencil to a curve -/

section Pencil

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

/-- The projective line over a field has dimension one. -/
private theorem topologicalKrullDim_projectiveSpaceOver_one (k : Type v) [Field k] :
    topologicalKrullDim (projectiveSpaceOver.{v} 1 (Spec (.of k))) = 1 := by
  let b := Finsupp.basisSingleOne (R := k) (ι := Fin 2)
  let e := Scheme.homeoOfIso ((Over.forget _).mapIso (basisProjectiveSpaceOfModuleIso b))
  have h : topologicalKrullDim (projectiveSpaceOfModule k (Fin 2 →₀ k)) = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by simp)
  exact e.isHomeomorph.topologicalKrullDim_eq.symm.trans h

/-- **A free pencil defines a fibration over a curve.** Let `X` be a normal projective variety
and `σ₁, σ₂` sections of `𝒪_X(M)`, `M` Cartier, with disjoint nonempty divisors of zeros. The
morphism `X ⟶ ℙ¹` they define has a Stein factorization `p : X ⟶ C` onto a smooth projective
curve with `p_* 𝒪_X = 𝒪_C`, and every irreducible closed subset of `X` missing `(σ₁)₀` or `(σ₂)₀`
is mapped by `p` to a point. -/
private theorem exists_curve_of_pencil {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] (hX : MMP.Mori.IsProjectiveVariety k sX)
    {M : Divisor X} (hM : M.IsCartier) (σ₁ σ₂ : M.divisorialSubmodule ⊤) (hσ₁ : σ₁ ≠ 0)
    (hσ₂ : σ₂ ≠ 0)
    (hdisj : Disjoint ((M.zeroDivisor σ₁ hσ₁).supp : Set X) (M.zeroDivisor σ₂ hσ₂).supp)
    (hne₁ : ((M.zeroDivisor σ₁ hσ₁).supp : Set X).Nonempty)
    (hne₂ : ((M.zeroDivisor σ₂ hσ₂).supp : Set X).Nonempty) :
    ∃ (C : Scheme.{v}) (_ : IsLocallyNoetherian C) (_ : IsNormal C) (_ : CompactSpace C)
      (sC : C ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sC)
      (_ : topologicalKrullDim C = 1) (_ : IsSmoothScheme sC) (p : X ⟶ C) (_ : p ≫ sC = sX)
      (_ : ∀ U : C.Opens, IsIso (p.app U)) (_ : Surjective p) (_ : IsProjectiveMorphism p),
      (∀ T : Set X, IsIrreducible T → IsClosed T →
        Disjoint T (M.zeroDivisor σ₁ hσ₁).supp → (p '' T).Subsingleton) ∧
      ∀ T : Set X, IsIrreducible T → IsClosed T →
        Disjoint T (M.zeroDivisor σ₂ hσ₂).supp → (p '' T).Subsingleton := by
  classical
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI := hM.isInvertibleModule_divisorialSheaf
  -- the pencil and the morphism `φ : X ⟶ ℙ¹` it defines
  set s : Fin 2 → Γ(M.divisorialSheaf, ⊤) := ![σ₁, σ₂] with hs_def
  have hnv₁ : ∀ x : X, x ∈ nvCover s 0 ↔ x ∉ ((M.zeroDivisor σ₁ hσ₁).supp : Set X) := fun x => by
    change x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ₁ ↔ _
    rw [Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ₁ hσ₁]
    rfl
  have hnv₂ : ∀ x : X, x ∈ nvCover s 1 ↔ x ∉ ((M.zeroDivisor σ₂ hσ₂).supp : Set X) := fun x => by
    change x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ₂ ↔ _
    rw [Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hM σ₂ hσ₂]
    rfl
  have hgen : GeneratesStalks s :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
      by_cases hx : x ∈ ((M.zeroDivisor σ₁ hσ₁).supp : Set X)
      · exact ⟨1, (hnv₂ x).2 (Set.disjoint_left.mp hdisj hx)⟩
      · exact ⟨0, (hnv₁ x).2 hx⟩
  set φ := toProjectiveSpaceOver s hgen sX with hφ
  let sP := CategoryTheory.Limits.pullback.fst
    (CategoryTheory.Limits.terminal.from (Spec (.of k)))
    (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{v} 1))
  have hφP : φ ≫ sP = sX := toProjectiveSpaceOver_fst _ _ _
  haveI : IsProper (φ ≫ sP) := by rw [hφP]; infer_instance
  haveI : IsProper φ := IsProper.of_comp φ sP
  have hpre : ∀ i, φ ⁻¹ᵁ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i = nvCover s i :=
    Stacks.AmpleImmersionReduction.preimage_standardChart s hgen φ
      (fun i => ι_toProjectiveSpaceOver s hgen sX i)
  -- the Stein factorization `φ = g ∘ q`
  obtain ⟨C, q, g, ⟨hS⟩, hqP, hqs, hqiso, -, hgfin, -, hYproj, hYnorm, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sP φ hφP
  have hcomp : q ≫ g = φ := hS.comp
  have hqg : ∀ x : X, g (q x) = φ x := fun x => by rw [← hcomp]; rfl
  set sC := g ≫ sP with hsC
  have hC : MMP.Mori.IsProjectiveVariety k sC :=
    hYproj (isProjectiveMorphism_projectiveSpaceOver 1 (Spec (.of k)))
  haveI : IsNormal C := hYnorm inferInstance
  haveI := hC.toIsIntegral
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  haveI : CompactSpace C := by
    haveI := hC.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sC
  have hps : q ≫ sC = sX := by rw [hsC, ← Category.assoc, hcomp, hφP]
  have hqproj : IsProjectiveMorphism q := by
    refine IsProjectiveMorphism.of_comp q sC ?_
    rw [hps]
    exact hX.isProjective
  -- two points of `X` with distinct images
  obtain ⟨x₁, hx₁⟩ := hne₁
  obtain ⟨x₂, hx₂⟩ := hne₂
  have hchart : ∀ i (x : X),
      φ x ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i ↔ x ∈ nvCover s i :=
    fun i x => by rw [← hpre i]; rfl
  have hx₁₀ : φ x₁ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 0 := fun h' =>
    (hnv₁ x₁).1 ((hchart 0 x₁).1 h') hx₁
  have hx₁₁ : φ x₁ ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 :=
    (hchart 1 x₁).2 ((hnv₂ x₁).2 (Set.disjoint_left.mp hdisj hx₁))
  have hx₂₁ : φ x₂ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) 1 := fun h' =>
    (hnv₂ x₂).1 ((hchart 1 x₂).1 h') hx₂
  have hq₁₂ : q x₁ ≠ q x₂ := fun h' => hx₂₁ (by rwa [← hqg, ← h', hqg])
  -- `C` is a curve
  obtain ⟨y₀, hy₀⟩ : ∃ y : C, y ≠ genericPoint C := by
    by_cases h' : q x₁ = genericPoint C
    · exact ⟨q x₂, fun h'' => hq₁₂ (h'.trans h''.symm)⟩
    · exact ⟨q x₁, h'⟩
  have hdimC : topologicalKrullDim C = 1 := by
    refine le_antisymm ((MMP.Fourfold.topologicalKrullDim_le_of_isFinite g
      (T := Set.univ) fun _ => trivial).trans ?_)
      (one_le_topologicalKrullDim_of_specializes_of_ne
        ((genericPoint_spec C).specializes trivial) (Ne.symm hy₀))
    rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq]
    exact (topologicalKrullDim_projectiveSpaceOver_one k).le
  have hCvar : MMP.Mori.IsVariety k sC := hC.toIsVariety
  have hCsm : IsSmoothScheme sC := by
    have hcl : ∀ y : C, y ≠ genericPoint C → y ∈ smoothLocus sC := fun y hy => by
      set Qy : MMP.Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimC hy)
      have hQy : Qy.genericPoint = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have := MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus (f := sC) hCvar Qy
      rwa [hQy] at this
    refine eq_top_iff.mpr fun y _ => ?_
    by_cases hy : y = genericPoint C
    · rw [hy]
      exact ((genericPoint_spec C).specializes trivial : genericPoint C ⤳ y₀).mem_open
        (smoothLocus sC).isOpen (hcl y₀ hy₀)
    · exact hcl y hy
  -- verticality
  have hvert : ∀ (i : Fin 2) (x₀ : X), φ x₀ ∉ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i →
      ∀ T : Set X, IsIrreducible T → IsClosed T → (∀ t ∈ T, t ∈ nvCover s i) →
        (q '' T).Subsingleton := by
    intro i x₀ hx₀ T hT hTc hTd
    have hI : IsIrreducible (q '' T) := hT.image q q.continuous.continuousOn
    have hcl : IsClosed (q '' T) := q.isClosedMap T hTc
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hI hcl
    by_cases hξg : ξ = genericPoint C
    · exfalso
      have hmem : q x₀ ∈ q '' T := by
        rw [← hξ.def, hξg, (genericPoint_spec C).def]; trivial
      obtain ⟨t, ht, hteq⟩ := hmem
      have h1 : φ t ∈ projectiveSpaceOver.standardChart 1 (Spec (.of k)) i :=
        (hchart i t).2 (hTd t ht)
      rw [← hqg, hteq, hqg] at h1
      exact hx₀ h1
    · have hcl' := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
        C hdimC hξg
      rw [← hξ.def, hcl'.closure_eq]
      exact Set.subsingleton_singleton
  refine ⟨C, inferInstance, inferInstance, inferInstance, sC, hC, hdimC, hCsm, q, hps, hqiso, hqs,
    hqproj, ?_, ?_⟩
  · intro T hT hTc hTd
    exact hvert 0 x₁ hx₁₀ T hT hTc fun t ht => (hnv₁ t).2 (Set.disjoint_left.mp hTd ht)
  · intro T hT hTc hTd
    exact hvert 1 x₂ hx₂₁ T hT hTc fun t ht => (hnv₂ t).2 (Set.disjoint_left.mp hTd ht)

end Pencil

/-! ### Sections of divisorial sheaves as rational functions -/

section Rational

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- The valuation along `E` of the component of a unit of `K(X)` is `exp (v_E φ)`. -/
private theorem valuation_component_eq_exp_ord (E : MMP.Mori.PrimeDivisor X)
    (φ : (RationalFunctions X)ˣ) :
    E.valuation ((φ : RationalFunctions X) E.component) = WithZero.exp (E.ord φ) := by
  rw [E.ord_eq_ordUnit, ← E.valuation_eq_exp_ordUnit]
  rfl

/-- A rational function `φ` with `div φ + D ≥ 0` is a global section of `𝒪_X(D)`. -/
private theorem symm_mem_divisorialSubmodule_of_nonneg {D : Divisor X}
    (φ : (RationalFunctions X)ˣ) (hφ : 0 ≤ principalDivisor φ + D) :
    (rationalFunctionsPresheafTopEquiv X).symm (φ : RationalFunctions X) ∈
      D.divisorialSubmodule ⊤ := by
  intro E _
  refine Or.inr ?_
  change WithZero.exp (-D.coeff E) ≤ E.valuation ((φ : RationalFunctions X) E.component)
  rw [valuation_component_eq_exp_ord, WithZero.exp_le_exp]
  have := hφ E
  change 0 ≤ (principalDivisor φ).coeff E + D.coeff E at this
  rw [coeff_principalDivisor] at this
  omega

/-- **A rational function with `div φ + D ≥ 0` is a section of `𝒪_X(D)`**, and its divisor of
zeros is `div φ + D`. -/
private theorem exists_section_of_nonneg {D : Divisor X} (φ : (RationalFunctions X)ˣ)
    (hφ : 0 ≤ principalDivisor φ + D) :
    ∃ (τ : D.divisorialSubmodule ⊤) (hτ : τ ≠ 0), D.zeroDivisor τ hτ = principalDivisor φ + D := by
  let e := rationalFunctionsPresheafTopEquiv X
  set τ : D.divisorialSubmodule ⊤ := ⟨_, symm_mem_divisorialSubmodule_of_nonneg φ hφ⟩
  have hτφ : Divisor.sectionToRationalFunctions τ = φ := e.apply_symm_apply _
  have hτ : τ ≠ 0 := fun h0 => by
    have h1 : Divisor.sectionToRationalFunctions τ = 0 := by
      rw [h0]
      exact map_zero e
    rw [hτφ] at h1
    haveI : Nontrivial (RationalFunctions X) :=
      (rationalFunctionsEquivFunctionField X).toEquiv.nontrivial
    exact φ.ne_zero h1
  refine ⟨τ, hτ, ?_⟩
  rw [Divisor.zeroDivisor_eq]
  congr 2
  exact Units.ext ((Divisor.isUnit_sectionToRationalFunctions hτ).unit_spec.trans hτφ)

end Rational

/-! ### Two sections with incomparable divisors of zeros -/

section Sections

variable {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- The global sections of `𝒪_X(D)`, `D` Cartier on a proper `k`-scheme, are a finite
`k`-module. -/
private theorem finite_divisorialSubmodule_top (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {D : Divisor X} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  exact finiteDimensional_globalSections k sX D.divisorialSheaf

/-- **Comparable divisors of zeros come from proportional sections.** If `(σ)₀ ≤ (σ')₀` for
nonzero sections of `𝒪_X(D)` on a proper normal variety over an algebraically closed field, then
`σ' = c σ` for a scalar `c`: the ratio `σ'/σ` has `div(σ'/σ) = (σ')₀ - (σ)₀ ≥ 0`, so it lies in
the finite `k`-algebra `H⁰(X, 𝒪_X)`, a domain, which is `k`. -/
private theorem exists_eq_smul_of_zeroDivisor_le (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {D : Divisor X} {σ σ' : D.divisorialSubmodule ⊤} (hσ : σ ≠ 0) (hσ' : σ' ≠ 0)
    (hle : D.zeroDivisor σ hσ ≤ D.zeroDivisor σ' hσ') :
    ∃ c : k, σ' = scalarsToGlobalSections k sX c • σ := by
  let T := ToType ((rationalFunctionsPresheaf X).obj (Opposite.op ⊤))
  let e := rationalFunctionsPresheafTopEquiv X
  set ψ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  set ψ' := (Divisor.isUnit_sectionToRationalFunctions hσ').unit
  have hu : 0 ≤ principalDivisor (ψ' * ψ⁻¹) + 0 := by
    have h := sub_nonneg.mpr hle
    rw [Divisor.zeroDivisor_eq, Divisor.zeroDivisor_eq] at h
    rw [add_zero, MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv]
    convert h using 1
    abel
  have hmem := symm_mem_divisorialSubmodule_of_nonneg _ hu
  have h1 : (1 : T) ∈ (0 : Divisor X).divisorialSubmodule ⊤ := by
    have := symm_mem_divisorialSubmodule_of_nonneg (D := (0 : Divisor X)) 1
      (by rw [MMP.Mori.principalDivisor_one, add_zero])
    exact (by simpa using this : Divisor.IsDivisorialSection 0 ⊤ 1)
  letI : Algebra k T := ((algebraMap Γ(X, ⊤) T).comp (scalarsToGlobalSections k sX)).toAlgebra
  let S : Subalgebra k T :=
    { carrier := (0 : Divisor X).divisorialSubmodule ⊤
      mul_mem' := fun {a b} ha hb => by
        have := Divisor.IsDivisorialSection.mul ha hb
        rwa [add_zero] at this
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      algebraMap_mem' := fun c => by
        change algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) ∈ _
        rw [← mul_one (algebraMap Γ(X, ⊤) T _), ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ h1 }
  letI := Module.compHom ((0 : Divisor X).divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  haveI := finite_divisorialSubmodule_top sX (Divisor.isCartier_zero (X := X))
  let g : ((0 : Divisor X).divisorialSubmodule ⊤) ≃ₗ[k] S :=
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun t => ⟨t.1, t.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite k S := Module.Finite.equiv g
  haveI : IsDomain T :=
    Function.Injective.isDomain (e.trans (rationalFunctionsEquivFunctionField X))
      (e.trans (rationalFunctionsEquivFunctionField X)).injective
  haveI : Algebra.IsIntegral k S := Algebra.IsIntegral.of_finite k S
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S)).2
    ⟨_, hmem⟩
  refine ⟨c, Subtype.ext ?_⟩
  have hc' :
      algebraMap k T c = e.symm ((ψ' * ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) :=
    congrArg Subtype.val hc
  change σ'.1 = algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) * σ.1
  rw [show algebraMap Γ(X, ⊤) T (scalarsToGlobalSections k sX c) = algebraMap k T c from rfl, hc']
  apply e.injective
  rw [map_mul, e.apply_symm_apply]
  have hψ : e σ.1 = (ψ : RationalFunctions X) :=
    ((Divisor.isUnit_sectionToRationalFunctions hσ).unit_spec).symm
  have hψ' : e σ'.1 = (ψ' : RationalFunctions X) :=
    ((Divisor.isUnit_sectionToRationalFunctions hσ').unit_spec).symm
  rw [hψ, hψ', Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- **Two sections of a linear system of dimension at least one.** If `h⁰(X, 𝒪_X(D)) ≥ 2` on a
normal projective variety over an algebraically closed field, there are nonzero sections
`σ₁, σ₂` of `𝒪_X(D)` neither of whose divisors of zeros is contained in the other: otherwise
`σ₂ / σ₁` would be a regular function on `X`, hence a constant. -/
private theorem exists_sections_not_le (hX : MMP.Mori.IsProjectiveVariety k sX) (D : Divisor X)
    (h2 : 2 ≤ D.h0 k sX) :
    ∃ (σ₁ σ₂ : D.divisorialSubmodule ⊤) (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0),
      ¬ D.zeroDivisor σ₁ hσ₁ ≤ D.zeroDivisor σ₂ hσ₂ ∧
        ¬ D.zeroDivisor σ₂ hσ₂ ≤ D.zeroDivisor σ₁ hσ₁ := by
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  have h2' : 1 < Module.finrank k (D.divisorialSubmodule ⊤) := h2
  haveI : Module.Finite k (D.divisorialSubmodule ⊤) :=
    Module.finite_of_finrank_pos (lt_trans zero_lt_one h2')
  haveI : Nontrivial (D.divisorialSubmodule ⊤) :=
    Module.nontrivial_of_finrank_pos (R := k) (lt_trans zero_lt_one h2')
  obtain ⟨σ₁, hσ₁⟩ := exists_ne (0 : D.divisorialSubmodule ⊤)
  obtain ⟨σ₂, hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2' hσ₁
  have hσ₂ : σ₂ ≠ 0 := by simpa using hli.ne_zero 1
  have hpair := LinearIndependent.pair_iff.mp hli
  refine ⟨σ₁, σ₂, hσ₁, hσ₂, fun hle => ?_, fun hle => ?_⟩
  · obtain ⟨c, hc⟩ := exists_eq_smul_of_zeroDivisor_le sX hσ₁ hσ₂ hle
    have := (hpair c (-1) (by
      change c • σ₁ + (-1 : k) • σ₂ = 0
      rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]
      exact hc.symm)).2
    exact one_ne_zero (neg_eq_zero.mp this)
  · obtain ⟨c, hc⟩ := exists_eq_smul_of_zeroDivisor_le sX hσ₂ hσ₁ hle
    have := (hpair (-1) c (by
      change (-1 : k) • σ₁ + c • σ₂ = 0
      rw [neg_one_smul, neg_add_eq_sub, sub_eq_zero]
      exact hc.symm)).1
    exact one_ne_zero (neg_eq_zero.mp this)

end Sections

/-! ### The moving part of the pencil -/

section Moving

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- **The moving part of a pencil.** Let `Z₂ = Z₁ + div ψ` be effective divisors and
`F = min(Z₁, Z₂)`. If `M₁ = Z₁ - F` and `M₂ = Z₂ - F` have disjoint supports, then `M₁` is Cartier
(it is `0` off `Supp M₁` and `-div ψ` off `Supp M₂`), and `1`, `ψ` are sections of `𝒪_X(M₁)` with
divisors of zeros `M₁` and `M₂`. -/
private theorem exists_sections_of_disjoint {Z₁ Z₂ : Divisor X} (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (ψ : (RationalFunctions X)ˣ) (hψ : Z₂ = principalDivisor ψ + Z₁)
    (hdisj : Disjoint ((Z₁ - Z₁ ⊓ Z₂).supp : Set X) (Z₂ - Z₁ ⊓ Z₂).supp) :
    (Z₁ - Z₁ ⊓ Z₂).IsCartier ∧ ∃ (τ₁ τ₂ : (Z₁ - Z₁ ⊓ Z₂).divisorialSubmodule ⊤) (hτ₁ : τ₁ ≠ 0)
      (hτ₂ : τ₂ ≠ 0), (Z₁ - Z₁ ⊓ Z₂).zeroDivisor τ₁ hτ₁ = Z₁ - Z₁ ⊓ Z₂ ∧
        (Z₁ - Z₁ ⊓ Z₂).zeroDivisor τ₂ hτ₂ = Z₂ - Z₁ ⊓ Z₂ := by
  set M₁ := Z₁ - Z₁ ⊓ Z₂
  set M₂ := Z₂ - Z₁ ⊓ Z₂
  have hM₁ : 0 ≤ M₁ := sub_nonneg.mpr inf_le_left
  have hM₂ : 0 ≤ M₂ := sub_nonneg.mpr inf_le_right
  have hM₂₁ : M₂ = principalDivisor ψ + M₁ := by
    simp only [M₁, M₂]
    rw [hψ]
    abel_nf
  -- a coefficient is zero along a prime divisor meeting the complement of the support
  have hcoeff : ∀ (G : Divisor X) (E : MMP.Mori.PrimeDivisor X),
      (E.support ∩ ((G.supp : Set X)ᶜ)).Nonempty → G.coeff E = 0 := by
    rintro G E ⟨x, hxE, hxG⟩
    by_contra hne
    exact hxG (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
  refine ⟨fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (M₁.supp : Set X)
    · have hx₂ : x ∉ (M₂.supp : Set X) := Set.disjoint_left.mp hdisj hx
      refine ⟨⟨(M₂.supp : Set X)ᶜ, M₂.isClosed_supp.isOpen_compl⟩, hx₂, ψ⁻¹, fun E hE => ?_⟩
      have h2 := hcoeff M₂ E hE
      have h3 := congrArg (fun G : Divisor X => G.coeff E) hM₂₁
      simp only [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, h2] at h3
      rw [MMP.Mori.PrimeDivisor.ord_inv]
      omega
    · refine ⟨⟨(M₁.supp : Set X)ᶜ, M₁.isClosed_supp.isOpen_compl⟩, hx, 1, fun E hE => ?_⟩
      rw [hcoeff M₁ E hE, MMP.Mori.PrimeDivisor.ord_one]
  · obtain ⟨τ₁, hτ₁, he₁⟩ := exists_section_of_nonneg (D := M₁) 1
      (by rwa [MMP.Mori.principalDivisor_one, zero_add])
    obtain ⟨τ₂, hτ₂, he₂⟩ := exists_section_of_nonneg (D := M₁) ψ (hM₂₁ ▸ hM₂)
    refine ⟨τ₁, τ₂, hτ₁, hτ₂, ?_, ?_⟩
    · rw [he₁, MMP.Mori.principalDivisor_one, zero_add]
    · rw [he₂, hM₂₁]

end Moving

/-! ### Triple intersection numbers on a threefold -/

section Triple

variable {k : Type v} [Field k] {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hX3 : topologicalKrullDim X = 3)

private theorem isCartier_update {E : Fin 3 → Divisor X} (hE : ∀ j, (E j).IsCartier) {G : Divisor X}
    (hG : G.IsCartier) (i : Fin 3) (j : Fin 3) : (Function.update E i G j).IsCartier := by
  rcases eq_or_ne j i with rfl | hj
  · simpa using hG
  · simpa [hj] using hE j

private theorem tri_add {E : Fin 3 → Divisor X} (hE : ∀ j, (E j).IsCartier) (i : Fin 3)
    {G G' : Divisor X} (hG : G.IsCartier) (hG' : G'.IsCartier) (h0 : E i = G + G') :
    Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E hE =
      Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le (Function.update E i G)
        (isCartier_update hE hG i) +
      Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le (Function.update E i G')
        (isCartier_update hE hG' i) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E j).divisorialSheaf :=
    fun j => (hE j).isInvertibleModule_divisorialSheaf
  haveI := hG.isInvertibleModule_divisorialSheaf
  haveI := hG'.isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  rw [intersectionNumber_update_tensor k sX (𝟙 X) 3 hX3.le i
    (fun j => (E j).divisorialSheaf) G.divisorialSheaf G'.divisorialSheaf
    (eqToIso (congrArg Divisor.divisorialSheaf h0) ≪≫ (hG.divisorialSheafTensorIso hG').symm)]
  have hfam : ∀ H : Divisor X,
      Function.update (fun j => (E j).divisorialSheaf) i H.divisorialSheaf =
      fun j => (Function.update E i H j).divisorialSheaf := fun H => funext fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  haveI := isInvertible_update (fun j => (E j).divisorialSheaf) i G.divisorialSheaf
  haveI := isInvertible_update (fun j => (E j).divisorialSheaf) i G'.divisorialSheaf
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update E i G j).divisorialSheaf :=
    fun j => (isCartier_update hE hG i j).isInvertibleModule_divisorialSheaf
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update E i G' j).divisorialSheaf :=
    fun j => (isCartier_update hE hG' i j).isInvertibleModule_divisorialSheaf
  exact congrArg₂ (· + ·)
    (intersectionNumber_congr_family k sX (𝟙 X) 3 hX3.le (hfam G))
    (intersectionNumber_congr_family k sX (𝟙 X) 3 hX3.le (hfam G'))

private theorem tri_congr {E E' : Fin 3 → Divisor X} (hE : ∀ j, (E j).IsCartier)
    (hE' : ∀ j, (E' j).IsCartier) (h : E = E') :
    Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E hE =
      Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E' hE' := by
  subst h
  rfl

private theorem tri_linEquiv {E : Fin 3 → Divisor X} (hE : ∀ j, (E j).IsCartier) (i : Fin 3)
    {G : Divisor X} (hG : G.IsCartier) (φ : (RationalFunctions X)ˣ)
    (h : E i = principalDivisor φ + G) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E hE =
      Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le (Function.update E i G)
        (isCartier_update hE hG i) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E j).divisorialSheaf :=
    fun j => (hE j).isInvertibleModule_divisorialSheaf
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update E i G j).divisorialSheaf :=
    fun j => (isCartier_update hE hG i j).isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_eq_of_iso_at k sX (𝟙 X) 3 hX3.le _ _ i
    (fun q hq => by simp only [Function.update_of_ne hq])
    (Divisor.divisorialSheafMulIso (D := E i) (D' := G) φ (fun E' => by
      rw [h, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, add_comm]) ≪≫
      eqToIso (by rw [Function.update_self]))

private theorem tri_perm {E : Fin 3 → Divisor X} (hE : ∀ j, (E j).IsCartier)
    (σ : Equiv.Perm (Fin 3)) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le (E ∘ σ) (fun j => hE (σ j)) =
      Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E hE := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E j).divisorialSheaf :=
    fun j => (hE j).isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_comp_perm k sX (𝟙 X) 3 hX3.le (fun j => (E j).divisorialSheaf) σ

open Opposite in
/-- Cutting an integral scheme by the pull-back of a global section of an invertible module that
does not vanish identically. -/
private theorem cut_pullback_section {C : Scheme.{v}} (j : C ⟶ X) [IsIntegral C] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (σ : Γ(M, ⊤))
    (hc : ∃ c : C, j c ∈ Stacks.Ample.nonvanishingLocus M σ) :
    ∃ (D : C.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D),
      Nonempty ((Scheme.Modules.pullback j).obj M ≅ Stacks.Divisors.invertibleSheaf D) := by
  have hs := MMP.Threefold.Mori.eval_pullbackSection_ne_zero j M σ hc
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback j).obj M)).symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection j M σ)
  have hinv0 : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback j).obj M) := inferInstance
  have hinv : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback j).obj M) := hinv0
  have hreg := isRegularSection_of_eval_top_ne_zero _ s hs
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme C _ s hreg).exists
  exact ⟨zeroScheme C _ (s.eval (op ⊤)),
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection C _ s).2 hreg, ⟨e.symm⟩⟩

/-- An integral closed subscheme is the reduced subscheme on the closure of its generic point. -/
private theorem eq_vanishingIdeal_closure_genericPoint (Z : X.IdealSheafData)
    [IsIntegral Z.subscheme] :
    Z = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({Z.subschemeι (genericPoint Z.subscheme)} : Set X)) := by
  have h := (genericPoint_spec Z.subscheme).image Z.subschemeι.continuous
  rw [Set.image_univ, Z.subschemeι.isClosedEmbedding.isClosed_range.closure_eq,
    Scheme.IdealSheafData.range_subschemeι] at h
  have hc : TopologicalSpace.Closeds.closure
      ({Z.subschemeι (genericPoint Z.subscheme)} : Set X) = Z.support :=
    TopologicalSpace.Closeds.ext h
  rw [hc]
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z Z.support rfl

/-- **Vanishing by cutting down.** If `E₀ ≥ 0` and `(E₁ · E₂ · V) = 0` for every surface
`V ⊆ X`, then `(E₀ · E₁ · E₂ · X) = 0`: cut `X` by the canonical section of `𝒪_X(E₀)`. -/
private theorem tri_eq_zero_of_nonneg [IsIntegral X] {E : Fin 3 → Divisor X}
    (hE : ∀ j, (E j).IsCartier) (h0 : 0 ≤ E 0)
    (hV : ∀ (x : X) (hV : topologicalKrullDim (curveSubschemeAt x) = 2),
      Divisor.intersectionNumberOn k sX (curveSubschemeAtι x) 2 hV.le (fun t => E t.succ)
        (fun t => hE t.succ) = 0) :
    Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le E hE = 0 := by
  haveI hinvE :
      ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E j).divisorialSheaf :=
    fun j => (hE j).isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hc : ∃ c : X, (𝟙 X : X ⟶ X) c ∈ Stacks.Ample.nonvanishingLocus (E 0).divisorialSheaf
      (MMP.Threefold.Mori.oneSection h0) := by
    refine ⟨genericPoint X, ?_⟩
    rw [MMP.Threefold.Mori.nonvanishingLocus_oneSection h0 (hE 0)]
    exact MMP.Fourfold.genericPoint_notMem_supp (E 0)
  obtain ⟨D, hD, ⟨e⟩⟩ := cut_pullback_section (𝟙 X) _ _ hc
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k sX (𝟙 X) 2 hX3.le _ D e,
    intersectionNumber_eq_sum_dimComponents]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  haveI := W.2.1
  have hW2 := W.2.2.2
  set ξ := W.1.subschemeι (genericPoint W.1.subscheme)
  have hWeq : Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({ξ} : Set X)) = W.1 :=
    (eq_vanishingIdeal_closure_genericPoint W.1).symm
  have hVξ : topologicalKrullDim (curveSubschemeAt ξ) = 2 := by
    change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({ξ} : Set X))).subscheme = 2
    rw [hWeq]
    exact hW2
  have h1 := hV ξ hVξ
  haveI : ∀ t : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (E t.succ).divisorialSheaf := fun t => hinvE t.succ
  unfold Divisor.intersectionNumberOn at h1
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h1
  have key : ∀ (Z : X.IdealSheafData) (_ : Z = W.1)
      (hd : topologicalKrullDim Z.subscheme ≤ (2 : ℕ)),
      intersectionNumber k sX Z.subschemeι 2 hd (fun t => (E t.succ).divisorialSheaf) =
        intersectionNumber k sX W.1.subschemeι 2 W.topologicalKrullDim_le
          (fun t => (E t.succ).divisorialSheaf) := by
    rintro Z rfl hd
    rfl
  rw [← key _ hWeq hVξ.le, h1, mul_zero]

end Triple

/-- **An effective ample divisor.** A projective variety carries an effective Cartier divisor `A`
with `𝒪_X(A)` ample: the divisor of a section of a power of an ample invertible sheaf. -/
private theorem exists_nonneg_isAmple {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]
    (hX : MMP.Mori.IsProjectiveVariety k sX) :
    ∃ A : Divisor X, 0 ≤ A ∧ ∃ hA : A.IsCartier, A.IsAmple hA := by
  obtain ⟨-, M, hMinv, hMamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX hX.isProjective.isHQuasiProjective
  have hM : Stacks.Ample.IsAmple X M :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX M hMamp
  obtain ⟨IX, hIX, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple M hM isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor IX hIX
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hH0, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple M n hn hM)⟩

section Vec

variable {X : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X]

private theorem isCartier_vec {a b c : Divisor X} (ha : a.IsCartier) (hb : b.IsCartier)
    (hc : c.IsCartier) : ∀ j, ((![a, b, c] : Fin 3 → Divisor X) j).IsCartier := by
  intro j; fin_cases j <;> simpa

private theorem update_vec_zero (a b c g : Divisor X) :
    Function.update (![a, b, c] : Fin 3 → Divisor X) 0 g = ![g, b, c] := by
  funext j; fin_cases j <;> simp

private theorem vec_comp_swap01 (a b c : Divisor X) :
    (![a, b, c] : Fin 3 → Divisor X) ∘ Equiv.swap 0 1 = ![b, a, c] := by
  funext j; fin_cases j <;> simp [Equiv.swap_apply_of_ne_of_ne]

private theorem vec_comp_swap02 (a b c : Divisor X) :
    (![a, b, c] : Fin 3 → Divisor X) ∘ Equiv.swap 0 2 = ![c, b, a] := by
  funext j; fin_cases j <;> simp [Equiv.swap_apply_of_ne_of_ne]

private theorem principalDivisor_pow' [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℕ) :
    principalDivisor (φ ^ n) = n • principalDivisor φ := by
  ext E
  change E.ord (φ ^ n) = (n • principalDivisor φ) E
  rw [Finsupp.smul_apply, MMP.Mori.PrimeDivisor.ord_pow]
  rfl

end Vec

section TripleIntersection

variable {k : Type v} [Field k] {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hX3 : topologicalKrullDim X = 3)

/-- The triple intersection number `(a · b · c · X)`. -/
private noncomputable abbrev tripleIntersection (a b c : Divisor X) (ha : a.IsCartier)
    (hb : b.IsCartier) (hc : c.IsCartier) : ℤ :=
  Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX3.le ![a, b, c] (isCartier_vec ha hb hc)

private theorem tripleIntersection_add_left {g g' b c : Divisor X} (hg : g.IsCartier)
    (hg' : g'.IsCartier) (hb : b.IsCartier) (hc : c.IsCartier) (hgg : (g + g').IsCartier) :
    tripleIntersection sX hX3 (g + g') b c hgg hb hc =
      tripleIntersection sX hX3 g b c hg hb hc + tripleIntersection sX hX3 g' b c hg' hb hc := by
  unfold tripleIntersection
  rw [tri_add sX hX3 _ 0 hg hg' rfl, tri_congr sX hX3 _ (isCartier_vec hg hb hc)
      (update_vec_zero _ _ _ _), tri_congr sX hX3 _ (isCartier_vec hg' hb hc)
      (update_vec_zero _ _ _ _)]

private theorem tripleIntersection_comm {a b c : Divisor X} (ha : a.IsCartier) (hb : b.IsCartier)
    (hc : c.IsCartier) :
    tripleIntersection sX hX3 a b c ha hb hc = tripleIntersection sX hX3 b a c hb ha hc := by
  unfold tripleIntersection
  rw [← tri_perm sX hX3 (isCartier_vec hb ha hc) (Equiv.swap 0 1)]
  exact tri_congr sX hX3 _ _ (vec_comp_swap01 _ _ _).symm

private theorem tripleIntersection_add_mid {a g g' c : Divisor X} (ha : a.IsCartier)
    (hg : g.IsCartier) (hg' : g'.IsCartier) (hc : c.IsCartier) (hgg : (g + g').IsCartier) :
    tripleIntersection sX hX3 a (g + g') c ha hgg hc =
      tripleIntersection sX hX3 a g c ha hg hc + tripleIntersection sX hX3 a g' c ha hg' hc := by
  rw [tripleIntersection_comm, tripleIntersection_add_left sX hX3 hg hg' ha hc hgg,
    tripleIntersection_comm sX hX3 hg, tripleIntersection_comm sX hX3 hg']

private theorem tripleIntersection_linEquiv_left {a a' b c : Divisor X} (ha : a.IsCartier)
    (ha' : a'.IsCartier) (hb : b.IsCartier) (hc : c.IsCartier) (φ : (RationalFunctions X)ˣ)
    (h : a = principalDivisor φ + a') :
    tripleIntersection sX hX3 a b c ha hb hc = tripleIntersection sX hX3 a' b c ha' hb hc := by
  unfold tripleIntersection
  rw [tri_linEquiv sX hX3 _ 0 ha' φ h]
  exact tri_congr sX hX3 _ _ (update_vec_zero _ _ _ _)

private theorem tripleIntersection_linEquiv_mid {a b b' c : Divisor X} (ha : a.IsCartier)
    (hb : b.IsCartier) (hb' : b'.IsCartier) (hc : c.IsCartier) (φ : (RationalFunctions X)ˣ)
    (h : b = principalDivisor φ + b') :
    tripleIntersection sX hX3 a b c ha hb hc = tripleIntersection sX hX3 a b' c ha hb' hc := by
  rw [tripleIntersection_comm, tripleIntersection_linEquiv_left sX hX3 hb hb' ha hc φ h,
    tripleIntersection_comm]

end TripleIntersection

/-! ### The intersection-theoretic core -/

section CoreProof

variable {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

private theorem exists_nsmul_isCartier (hQ : MMP.Fourfold.IsQFactorial sX)
    (s : Finset (Divisor X)) : ∃ N : ℕ, 0 < N ∧ ∀ G ∈ s, (N • G).IsCartier := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert G s _ ih =>
    obtain ⟨N, hN, hs⟩ := ih
    obtain ⟨n, hn, hG⟩ := hQ.2 G
    rw [natCast_zsmul] at hG
    refine ⟨N * n, Nat.mul_pos hN hn, fun G' hG' => ?_⟩
    rcases Finset.mem_insert.mp hG' with rfl | hG'
    · rw [← smul_smul]
      exact hG.nsmul N
    · rw [mul_comm, ← smul_smul]
      exact (hs G' hG').nsmul n

private theorem toQDivisor_apply (G : Divisor X) (E : MMP.Mori.PrimeDivisor X) :
    (Divisor.toQDivisor G) E = (G E : ℚ) := by
  rw [← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply]

private theorem isEffective_toQDivisor {G : Divisor X} (hG : 0 ≤ G) :
    (Divisor.toQDivisor G).IsEffective := fun E => by
  rw [DivisorWithCoeffs.coeff_apply, toQDivisor_apply]
  exact_mod_cast hG E

private theorem toQDivisor_nsmul (N : ℕ) (G : Divisor X) :
    Divisor.toQDivisor (N • G) = (N : ℚ) • Divisor.toQDivisor G := by
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]

private theorem nonneg_of_div_nonneg {x : ℤ} {p : ℚ} (hp : 0 < p) (h : 0 ≤ (x : ℚ) / p) :
    0 ≤ x := by
  have := mul_nonneg h hp.le
  rw [div_mul_cancel₀ _ hp.ne'] at this
  exact_mod_cast this

private theorem intersectionNumberOn_congr {Z : Scheme.{v}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsProper sX] {d : ℕ} (hd : topologicalKrullDim Z ≤ d) {E E' : Fin d → Divisor X}
    (hE : ∀ j, (E j).IsCartier) (hE' : ∀ j, (E' j).IsCartier) (h : E = E') :
    Divisor.intersectionNumberOn k sX i d hd E hE =
      Divisor.intersectionNumberOn k sX i d hd E' hE' := by
  subst h
  rfl

/-- **General members of the pencil are disjoint.** -/
private theorem disjoint_of_intersection (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hX3 : topologicalKrullDim X = 3) (hQ : MMP.Fourfold.IsQFactorial sX) {L : QDivisor X}
    (hL : L.IsNef k sX) {m : ℕ} (hm : 0 < m) {D : Divisor X} (hDc : D.IsCartier)
    (hDL : Divisor.toQDivisor D = (m : ℤ) • L)
    (hν : haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
      ∀ (x : X) (hV : topologicalKrullDim (curveSubschemeAt x) = 2) (E : Divisor X)
        (hE : E.IsCartier) (m' : ℕ), 0 < m' → Divisor.toQDivisor E = (m' : ℚ) • L →
        Divisor.intersectionNumberOn k sX (curveSubschemeAtι x) 2 hV.le (fun _ => E)
          (fun _ => hE) = 0)
    {Z₁ Z₂ : Divisor X} (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂) (ψ₁ ψ₂ : (RationalFunctions X)ˣ)
    (hψ₁ : Z₁ = principalDivisor ψ₁ + D) (hψ₂ : Z₂ = principalDivisor ψ₂ + D) :
    Disjoint ((Z₁ - Z₁ ⊓ Z₂).supp : Set X) (Z₂ - Z₁ ⊓ Z₂).supp ∧
      ∀ E : MMP.Mori.PrimeDivisor X, (Z₁ ⊓ Z₂) E ≠ 0 →
        Disjoint (E.support : Set X) (Z₁ - Z₁ ⊓ Z₂).supp ∨
          Disjoint (E.support : Set X) (Z₂ - Z₁ ⊓ Z₂).supp := by
  classical
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  set F := Z₁ ⊓ Z₂
  set M₁ := Z₁ - F with hM₁def
  set M₂ := Z₂ - F with hM₂def
  set Fa := F.filter (fun E => M₁ E = 0) with hFadef
  set Fb := F.filter (fun E => ¬ M₁ E = 0) with hFbdef
  have hFab : Fa + Fb = F := Finsupp.filter_pos_add_filter_neg F _
  have hF0 : 0 ≤ F := le_inf hZ₁ hZ₂
  have hM₁0 : 0 ≤ M₁ := sub_nonneg.mpr inf_le_left
  have hM₂0 : 0 ≤ M₂ := sub_nonneg.mpr inf_le_right
  have hFa0 : 0 ≤ Fa := fun E => by
    simp only [Fa, Finsupp.filter_apply]
    split_ifs <;> first | exact hF0 E | exact le_rfl
  have hFb0 : 0 ≤ Fb := fun E => by
    simp only [Fb, Finsupp.filter_apply]
    split_ifs <;> first | exact hF0 E | exact le_rfl
  have hmin : ∀ E, M₁ E = 0 ∨ M₂ E = 0 := fun E => by
    simp only [M₁, M₂, F, Finsupp.coe_sub, Pi.sub_apply, Finsupp.inf_apply]
    omega
  -- Cartier multiples
  obtain ⟨N, hN, hNc⟩ := exists_nsmul_isCartier hQ {M₁, M₂, Fa, Fb}
  have hP := hNc M₁ (by simp)
  have hQc := hNc M₂ (by simp)
  have hPa := hNc Fa (by simp)
  have hPb := hNc Fb (by simp)
  have hΔ := hDc.nsmul N
  obtain ⟨A, hA0, hAc, hAa⟩ := exists_nonneg_isAmple hX
  have hH : (haveI := QuasiCompact.compactSpace_of_compactSpace sX
      (Divisor.toQDivisor A).IsAmple) := ⟨1, one_pos, A, by simp, hAc, hAa⟩
  obtain ⟨lib1, lib2⟩ := MMP.Flips.intersectionNumberOn_nonneg_of_isEffective k sX hX3 hH
  -- the relations
  have hZ₁N : N • Z₁ = N • M₁ + (N • Fa + N • Fb) := by
    rw [← smul_add, ← smul_add, hFab, hM₁def, sub_add_cancel]
  have hZΔ : N • M₁ + (N • Fa + N • Fb) = principalDivisor (ψ₁ ^ N) + N • D := by
    rw [← hZ₁N, hψ₁, smul_add, principalDivisor_pow']
  have hQP : N • M₂ = principalDivisor ((ψ₂ * ψ₁⁻¹) ^ N) + N • M₁ := by
    rw [principalDivisor_pow', MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv,
      ← smul_add, hM₁def, hM₂def, hψ₂, hψ₁]
    congr 1
    abel
  have hPQ : N • M₁ = principalDivisor ((ψ₂ * ψ₁⁻¹) ^ N)⁻¹ + N • M₂ := by
    rw [MMP.Mori.principalDivisor_inv, hQP]
    abel
  have tΔ : Divisor.toQDivisor (N • D) = ((N * m : ℕ) : ℚ) • L := by
    rw [toQDivisor_nsmul, hDL, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rfl
  have hprod : ∀ a b : ℕ, 0 < a → 0 < b →
      (0 : ℚ) < ∏ j, (((![a, b, 1] : Fin 3 → ℕ) j : ℕ) : ℚ) := fun a b ha hb =>
    Finset.prod_pos fun j _ => by fin_cases j <;> simp [ha, hb]
  -- nonnegativity against the nef `L`
  have hnef : ∀ {G : Divisor X} (hG0 : 0 ≤ G) (hGc : (N • G).IsCartier),
      0 ≤ tripleIntersection sX hX3 (N • G) (N • D) A hGc hΔ hAc := fun {G} hG0 hGc => by
    have h := lib2 (Divisor.toQDivisor G) L (isEffective_toQDivisor hG0) hL ![N • G, N • D, A]
      (isCartier_vec hGc hΔ hAc) ![N, N * m, 1]
      (fun j => by fin_cases j <;> simp [hN, hm])
      (fun j => by
        fin_cases j
        · simp [toQDivisor_nsmul]
        · simpa using tΔ
        · simp)
    exact nonneg_of_div_nonneg (hprod N (N * m) hN (Nat.mul_pos hN hm)) h
  -- the effective pairs without common components
  have hpair : ∀ {G₁ G₂ : Divisor X} (h₁ : 0 ≤ G₁) (h₂ : 0 ≤ G₂)
      (hd : ∀ E, G₁ E = 0 ∨ G₂ E = 0) (hc₁ : (N • G₁).IsCartier) (hc₂ : (N • G₂).IsCartier),
      0 ≤ tripleIntersection sX hX3 (N • G₁) (N • G₂) A hc₁ hc₂ hAc ∧
        (tripleIntersection sX hX3 (N • G₁) (N • G₂) A hc₁ hc₂ hAc = 0 ↔
          Disjoint (G₁.supp : Set X) G₂.supp) := fun {G₁ G₂} h₁ h₂ hd hc₁ hc₂ => by
    have hdisj : Disjoint (Divisor.toQDivisor G₁).support (Divisor.toQDivisor G₂).support := by
      rw [Finset.disjoint_left]
      intro E hE1 hE2
      rw [Finsupp.mem_support_iff, toQDivisor_apply] at hE1 hE2
      rcases hd E with h | h <;> simp_all
    obtain ⟨h1, h2⟩ := lib1 _ _ (isEffective_toQDivisor h₁) (isEffective_toQDivisor h₂) hdisj
      ![N • G₁, N • G₂, A] (isCartier_vec hc₁ hc₂ hAc) ![N, N, 1]
      (fun j => by fin_cases j <;> simp [hN])
      (fun j => by fin_cases j <;> simp [toQDivisor_nsmul])
    rw [div_eq_zero_iff, or_iff_left (hprod N N hN hN).ne', Int.cast_eq_zero,
      Divisor.supp_toQDivisor, Divisor.supp_toQDivisor] at h2
    exact ⟨nonneg_of_div_nonneg (hprod N N hN hN) h1, h2⟩
  -- `(D · D · A) = 0`
  have hzero : tripleIntersection sX hX3 (N • D) (N • D) A hΔ hΔ hAc = 0 := by
    unfold tripleIntersection
    rw [← tri_perm sX hX3 (isCartier_vec hAc hΔ hΔ) (Equiv.swap 0 2) |>.symm.trans
      (tri_congr sX hX3 _ (isCartier_vec hΔ hΔ hAc) (vec_comp_swap02 _ _ _))]
    refine tri_eq_zero_of_nonneg sX hX3 (isCartier_vec hAc hΔ hΔ) (by simpa using hA0)
      fun x hV => ?_
    rw [intersectionNumberOn_congr (curveSubschemeAtι x) hV.le _ (fun _ => hΔ)
      (by funext t; fin_cases t <;> rfl)]
    exact hν x hV (N • D) hΔ (N * m) (Nat.mul_pos hN hm) tΔ
  -- `M₁ · D · A = 0`
  have hsum := hPa.add hPb
  have hall := hP.add hsum
  have ha : tripleIntersection sX hX3 (N • M₁) (N • D) A hP hΔ hAc = 0 := by
    have e1 := tripleIntersection_linEquiv_left sX hX3 hall hΔ hΔ hAc (ψ₁ ^ N) hZΔ
    rw [hzero, tripleIntersection_add_left sX hX3 hP hsum hΔ hAc hall,
      tripleIntersection_add_left sX hX3 hPa hPb hΔ hAc hsum] at e1
    have := hnef hM₁0 hP
    have := hnef hFa0 hPa
    have := hnef hFb0 hPb
    omega
  -- `M₁ · M₂ · A + M₁ · F_a · A + M₂ · F_b · A = 0`
  have hFaM : ∀ E, M₁ E = 0 ∨ Fa E = 0 := fun E => by
    by_cases h : M₁ E = 0
    · exact Or.inl h
    · exact Or.inr (by simp [Fa, Finsupp.filter_apply, h])
  have hFbM : ∀ E, M₂ E = 0 ∨ Fb E = 0 := fun E => by
    by_cases h : M₁ E = 0
    · exact Or.inr (by simp [Fb, Finsupp.filter_apply, h])
    · exact Or.inl ((hmin E).resolve_left h)
  obtain ⟨c0, ciff⟩ := hpair hM₁0 hM₂0 hmin hP hQc
  obtain ⟨d10, d1iff⟩ := hpair hM₁0 hFa0 hFaM hP hPa
  obtain ⟨d20, d2iff⟩ := hpair hM₂0 hFb0 hFbM hQc hPb
  have hc : tripleIntersection sX hX3 (N • M₁) (N • M₂) A hP hQc hAc =
      tripleIntersection sX hX3 (N • M₁) (N • M₁) A hP hP hAc := by
    rw [tripleIntersection_comm, tripleIntersection_linEquiv_left sX hX3 hQc hP hP hAc _ hQP]
  have e2 := tripleIntersection_linEquiv_mid sX hX3 hP hall hΔ hAc (ψ₁ ^ N) hZΔ
  rw [ha, tripleIntersection_add_mid sX hX3 hP hP hsum hAc hall,
    tripleIntersection_add_mid sX hX3 hP hPa hPb hAc hsum,
    tripleIntersection_linEquiv_left sX hX3 hP hQc hPb hAc _ hPQ, ← hc] at e2
  have hc0 : tripleIntersection sX hX3 (N • M₁) (N • M₂) A hP hQc hAc = 0 := by omega
  have hd1 : tripleIntersection sX hX3 (N • M₁) (N • Fa) A hP hPa hAc = 0 := by omega
  have hd2 : tripleIntersection sX hX3 (N • M₂) (N • Fb) A hQc hPb hAc = 0 := by omega
  refine ⟨ciff.1 hc0, fun E hE => ?_⟩
  have hgen : ∀ (G : Divisor X), G E ≠ 0 → (E.support : Set X) ⊆ G.supp := fun G hG x hx =>
    DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hG, hx⟩
  by_cases h : M₁ E = 0
  · left
    have : Fa E ≠ 0 := by rwa [hFadef, Finsupp.filter_apply, if_pos h]
    exact (d1iff.1 hd1).symm.mono_left (hgen _ this)
  · right
    have : Fb E ≠ 0 := by rwa [hFbdef, Finsupp.filter_apply, if_pos h]
    exact (d2iff.1 hd2).symm.mono_left (hgen _ this)

end CoreProof

/-! ### Divisors on a smooth projective curve and their pull-backs -/

section CurveDivisors

/-- A closed embedding `f : Y → X` into an irreducible space with `dim X ≤ n ≤ dim Y` is
surjective: otherwise the image of a chain of length `n` in `Y`, followed by `X`, is a chain
of length `n + 1` in `X`. -/
private theorem surjective_of_topologicalKrullDim_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace X] {f : Y → X} (hf : Topology.IsClosedEmbedding f)
    {n : ℕ} (hX : topologicalKrullDim X ≤ n) (hY : (n : WithBot ℕ∞) ≤ topologicalKrullDim Y) :
    Function.Surjective f := by
  by_contra hns
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hY
  let φ : TopologicalSpace.IrreducibleCloseds Y → TopologicalSpace.IrreducibleCloseds X :=
    fun Z => ⟨f '' Z, Z.isIrreducible.image f hf.continuous.continuousOn,
      hf.isClosedMap _ Z.isClosed⟩
  have hφ : StrictMono φ := fun a b hab =>
    (hf.injective.image_strictMono : StrictMono (f '' ·)) (show (a : Set Y) < b from hab)
  let top : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : φ l.last < top := by
    change f '' (l.last : Set Y) < Set.univ
    exact lt_of_le_of_lt (Set.image_subset_range f _)
      (Set.ssubset_univ_iff.mpr fun h => hns (Set.range_eq_univ.mp h))
  have h := Order.LTSeries.length_le_krullDim ((l.map φ hφ).snoc top hlt)
  have hlen : ((l.map φ hφ).snoc top hlt).length = n + 1 := by
    change l.length + 1 = n + 1
    omega
  rw [hlen] at h
  exact absurd (h.trans hX) (by exact_mod_cast Nat.not_succ_le_self n)

/-- **An effective nonzero Cartier divisor on a projective curve is ample**, by the Nakai
criterion: its degree on the curve is positive. -/
private theorem isAmple_of_nonneg_of_ne_zero {k : Type v} [Field k] {C : Scheme.{v}}
    [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C] [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdim : topologicalKrullDim C = 1) (A : Divisor C) (hAc : A.IsCartier) (h0 : 0 ≤ A)
    (hne : A ≠ 0) : A.IsAmple hAc := by
  haveI : IsProper sC := isProper_of_isProjectiveMorphism sC hC.isProjective
  haveI := hAc.isInvertibleModule_divisorialSheaf
  have hP : IsProjective sC := ((isProjectiveVariety_iff_isProjective' k sC).1 hC).2
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos k sC hP _
    fun V i _ _ d hd hd0 => ?_
  have hVS : topologicalKrullDim V ≤ 1 :=
    ((topologicalKrullDim_range_eq i).symm.le.trans (topologicalKrullDim_subspace_le C _)).trans
      hdim.le
  have hd1 : d ≤ 1 := by
    rw [hd] at hVS
    exact_mod_cast hVS
  obtain rfl : d = 1 := by omega
  have hV : topologicalKrullDim V = 1 := by rw [hd]; rfl
  have hsurj : Function.Surjective i := surjective_of_topologicalKrullDim_le i.isClosedEmbedding
    (n := 1) (by rw [hdim]; rfl) (by rw [hd])
  obtain ⟨E, hE⟩ := DFunLike.ne_iff.mp hne
  have hEx : E.genericPoint ∈ (A.supp : Set C) := DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  obtain ⟨c₁, hc₁⟩ := hsurj E.genericPoint
  obtain ⟨c₀, hc₀⟩ := hsurj (genericPoint C)
  obtain ⟨hnn, hiff⟩ := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sC i hV.le A hAc h0
    ⟨c₀, by rw [hc₀]; exact MMP.Fourfold.genericPoint_notMem_supp A⟩
  have hpos : 0 < A.degreeOn k sC i hV.le hAc :=
    lt_of_le_of_ne hnn fun h => hiff.1 h.symm c₁ (by rw [hc₁]; exact hEx)
  have h3 : A.degreeOn k sC i hV.le hAc =
      invertibleCurveDegree k (i ≫ sC) hV.le ((Scheme.Modules.pullback i).obj A.divisorialSheaf) :=
    rfl
  rw [h3, ← intersectionNumber_one_eq_invertibleCurveDegree] at hpos
  rw [sheafSelfIntersectionNumber, Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact hpos

variable {X C : Scheme.{v}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
  (hC : topologicalKrullDim C = 1) (p : X ⟶ C)
  (hη : ∀ (D : Divisor C) (Z : irreducibleComponents X), p (componentGenericPoint X Z) ∉ D.supp)
  (hcart : ∀ D : Divisor C, D.IsCartier)

include hC in
/-- On a curve the generic point of a prime divisor is a closed point. -/
private theorem isClosed_singleton_genericPoint (Q : MMP.Mori.PrimeDivisor C) :
    IsClosed ({Q.genericPoint} : Set C) :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hC
    fun h => by
      have h1 := Q.coheight_genericPoint
      rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        at h1
      exact zero_ne_one h1

include hC hcart in
/-- **The coefficients of a pull-back from a curve.** If `p(η_E) = η_Q`, the coefficient of
`p^*G` along `E` is `G(Q) · (p^*Q)(E)`. -/
private theorem coeff_isPullback_eq_mul {G : Divisor C} {G' : Divisor X}
    (hG' : G.IsPullback p (hη G) G') (E : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor C) (hEQ : p E.genericPoint = Q.genericPoint) :
    G'.coeff E = G.coeff Q *
      (Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)).coeff E := by
  classical
  set F : MMP.Mori.PrimeDivisor C → Divisor X := fun Q =>
    Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)
  have hF : ∀ Q, Divisor.IsPullback p (Finsupp.single Q 1 : Divisor C) (hη _) (F Q) := fun Q =>
    Divisor.isPullback_pullback (hcart _) (hη _)
  have hGsum : G = ∑ Q ∈ G.support, G Q • (Finsupp.single Q 1 : Divisor C) := by
    refine Finsupp.ext fun Q => ?_
    simp only [Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h)
  have hpb := (MMP.Fourfold.isPullback_sum_smul_single p hη hcart F hF G.support G).of_eq
    hGsum.symm (hB₂ := hη G)
  have hG'eq : G' = ∑ Q ∈ G.support, G Q • F Q := hG'.eq (hcart G) hpb
  have hcoeff : G'.coeff E = ∑ Q' ∈ G.support, G Q' * (F Q').coeff E := by
    rw [hG'eq]
    simp only [DivisorWithCoeffs.coeff_apply, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [hcoeff, Finset.sum_eq_single Q]
  · rfl
  · intro Q' _ hQ'
    rw [MMP.Fourfold.coeff_eq_zero_of_isPullback_single p Q'
      (isClosed_singleton_genericPoint hC Q') (hF Q') E fun h => hQ'
        (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h.symm.trans hEQ)), mul_zero]
  · intro hQ
    rw [Finsupp.notMem_support_iff.mp hQ, zero_mul]

include hC hη hcart in
/-- Over every closed point of the curve there is a prime divisor of `X`. -/
private theorem exists_primeDivisor_genericPoint_eq [Surjective p]
    (Q : MMP.Mori.PrimeDivisor C) :
    ∃ E : MMP.Mori.PrimeDivisor X, p E.genericPoint = Q.genericPoint := by
  obtain ⟨x, hx⟩ := p.surjective Q.genericPoint
  have hF := Divisor.isPullback_pullback (f := p) (hcart (Finsupp.single Q 1 : Divisor C))
    (hη _)
  have hxs := MMP.Fourfold.mem_supp_of_isPullback_single p Q hF hx
  obtain ⟨E, hE, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxs
  by_contra h
  push Not at h
  exact hE (MMP.Fourfold.coeff_eq_zero_of_isPullback_single p Q
    (isClosed_singleton_genericPoint hC Q) hF E (h E))

include hη hcart in
/-- `p^*(q B) = q p^*B` for a divisor `B` on `C` and `q ∈ ℚ`. -/
private theorem isPullback_smul_toQDivisor {B : Divisor C} {B' : Divisor X}
    (hB' : B.IsPullback p (hη B) B') (q : ℚ)
    (hBq : ∀ Z : irreducibleComponents X,
      p (componentGenericPoint X Z) ∉ (q • Divisor.toQDivisor B).supp) :
    (q • Divisor.toQDivisor B).IsPullback p hBq (q • Divisor.toQDivisor B') := by
  intro m hm D hD hDc
  refine ⟨D.pullback hDc (hη D), ?_, Divisor.isPullback_pullback hDc (hη D)⟩
  have key : (q.den : ℤ) • D = ((m : ℤ) * q.num) • B := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_zsmul, hD]
    ext E
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul]
    push_cast
    have := Rat.mul_den_eq_num q
    rw [← this]
    ring
  have h1 := (Divisor.isPullback_pullback hDc (hη D)).zsmul hDc (q.den : ℤ) (hη _)
  have h2 := (hB'.zsmul (hcart B) ((m : ℤ) * q.num) (hη _)).of_eq key.symm (hB₂ := hη _)
  have h3 : (q.den : ℤ) • D.pullback hDc (hη D) = ((m : ℤ) * q.num) • B' :=
    h1.eq (hDc.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul] at h4
  ext E
  have h5 := congrArg (fun G : QDivisor X => G.coeff E) h4
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul] at h5 ⊢
  push_cast at h5
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  conv_rhs => rw [← Rat.num_div_den q]
  field_simp
  linear_combination h5

end CurveDivisors

/-! ### Descent to the curve -/

section Descent

variable {k : Type v} [Field k] [IsAlgClosed k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- **Descent of the pencil to the curve.** In the situation of `disjoint_of_intersection`, let
`p : X ⟶ C` be the fibration of the free pencil `|M₁|` onto a smooth projective curve with
`p_* 𝒪_X = 𝒪_C`, such that irreducible closed sets missing `Supp M₁` or `Supp M₂` lie in fibres.
Then every component of `Z₁ = M₁ + F` is vertical. For a divisor `G` on `C` with `p^*G ≥ Z₁`,
`A = p^*G - Z₁` is effective and vertical, and `-A ∼ D - p^*G` is `p`-nef since `D = mL` is nef
and `p^*G` is trivial on the fibres; Zariski's lemma
(`MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`) gives `A = p^*P`. So
`Z₁ = p^*(G - P)`, `L ∼_ℚ p^*N` with `N = (G - P)/m`, and `G - P` is effective and nonzero, hence
ample on the curve. -/
private theorem exists_pullback_of_pencil [CharZero k] (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hQ : MMP.Fourfold.IsQFactorial sX) {L : QDivisor X} (hL : L.IsNef k sX) {m : ℕ}
    (hm : 0 < m) {D : Divisor X} (hDc : D.IsCartier) (hDL : Divisor.toQDivisor D = (m : ℤ) • L)
    {Z₁ Z₂ : Divisor X} (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂) (ψ₁ ψ : (RationalFunctions X)ˣ)
    (hψ₁ : Z₁ = principalDivisor ψ₁ + D) (hψ : Z₂ = principalDivisor ψ + Z₁)
    (hne : Z₁ - Z₁ ⊓ Z₂ ≠ 0)
    (hdisj : Disjoint ((Z₁ - Z₁ ⊓ Z₂).supp : Set X) (Z₂ - Z₁ ⊓ Z₂).supp)
    (hF : ∀ E : MMP.Mori.PrimeDivisor X, (Z₁ ⊓ Z₂) E ≠ 0 →
      Disjoint (E.support : Set X) (Z₁ - Z₁ ⊓ Z₂).supp ∨
        Disjoint (E.support : Set X) (Z₂ - Z₁ ⊓ Z₂).supp)
    {C : Scheme.{v}} [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (sC : C ⟶ Spec (.of k)) (hC : MMP.Mori.IsProjectiveVariety k sC)
    (hdimC : topologicalKrullDim C = 1) (hCsm : IsSmoothScheme sC) (p : X ⟶ C) (hps : p ≫ sC = sX)
    (hp : ∀ U : C.Opens, IsIso (p.app U)) [Surjective p] (hpp : IsProjectiveMorphism p)
    (hvert₁ : ∀ T : Set X, IsIrreducible T → IsClosed T →
      Disjoint T (Z₁ - Z₁ ⊓ Z₂).supp → (p '' T).Subsingleton)
    (hvert₂ : ∀ T : Set X, IsIrreducible T → IsClosed T →
      Disjoint T (Z₂ - Z₁ ⊓ Z₂).supp → (p '' T).Subsingleton) :
    ∃ (N : QDivisor C) (hN : N.IsQCartier) (n : ℕ) (_ : 0 < n) (A : Divisor C)
      (_ : Divisor.toQDivisor A = (n : ℚ) • N) (hAc : A.IsCartier) (_ : A.IsAmple hAc),
      ∃ hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp,
        L.QLinearlyEquivalent (N.pullback hN hB) := by
  classical
  haveI := hC.toIsIntegral
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : IsProper p := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hpp).2
  set F := Z₁ ⊓ Z₂
  set M₁ := Z₁ - F with hM₁def
  set M₂ := Z₂ - F with hM₂def
  -- `p` maps the generic point of `X` to that of `C`
  have hgenX : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) = genericPoint C := by
    intro Z
    have hZ : Z.1 = Set.univ := by
      have h : Z.1 ∈ ({Set.univ} : Set (Set X)) :=
        (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
      exact h
    have hgp := isGenericPoint_componentGenericPoint X Z
    rw [hZ] at hgp
    refine IsGenericPoint.eq ?_ (genericPoint_spec C)
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := p.surjective y
    have hx : x ∈ closure {componentGenericPoint X Z} := by rw [hgp.def]; trivial
    have := image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  have hη : ∀ (G : Divisor C) (Z : irreducibleComponents X),
      p (componentGenericPoint X Z) ∉ G.supp := fun G Z => by
    rw [hgenX]; exact MMP.Fourfold.genericPoint_notMem_supp G
  have hcart : ∀ G : Divisor C, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hCsm
  have hmemη : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ (E.support : Set X) := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hsub : ∀ (G : Divisor X) (E : MMP.Mori.PrimeDivisor X), G E ≠ 0 →
      (E.support : Set X) ⊆ G.supp := fun G E hG x hx =>
    DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hG, hx⟩
  have hF0 : 0 ≤ F := le_inf hZ₁ hZ₂
  -- the components of `Z₁` are vertical
  have hvertZ : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 →
      (p '' (E.support : Set X)).Subsingleton := by
    intro E hE
    have hirr : IsIrreducible (E.support : Set X) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    have hcl : IsClosed (E.support : Set X) := E.idealSheaf.support.isClosed
    by_cases hM : M₁ E = 0
    · have hFE : F E ≠ 0 := by
        intro h0
        apply hE
        have : M₁ E = Z₁ E - F E := rfl
        omega
      rcases hF E hFE with h | h
      · exact hvert₁ _ hirr hcl h
      · exact hvert₂ _ hirr hcl h
    · exact hvert₂ _ hirr hcl (hdisj.mono_left (hsub M₁ E hM))
  have hvertpt : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 →
      ∀ x ∈ (E.support : Set X), p x = p E.genericPoint := fun E hE x hx =>
    hvertZ E hE ⟨x, hx, rfl⟩ ⟨_, hmemη E, rfl⟩
  have hnotgen : ∀ E : MMP.Mori.PrimeDivisor X, Z₁ E ≠ 0 → p E.genericPoint ≠ genericPoint C := by
    intro E hE h
    have himg : p '' (E.support : Set X) = {p E.genericPoint} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨E.genericPoint, hmemη E, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩; exact hvertpt E hE x hx
    have hcl := p.isClosedMap _ E.idealSheaf.support.isClosed
    change IsClosed (p '' (E.support : Set X)) at hcl
    rw [himg, h] at hcl
    exact MMP.Fourfold.not_isClosed_genericPoint hdimC hcl
  -- the points of `C` below the components of `Z₁`, and a pull-back `G' = p^*G ≥ Z₁`
  set T : Set (MMP.Mori.PrimeDivisor C) :=
    {Q | ∃ E, Z₁ E ≠ 0 ∧ p E.genericPoint = Q.genericPoint}
  have hT : T.Finite :=
    ((Z₁.support.finite_toSet.image fun E => p E.genericPoint).preimage
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn).subset
      fun Q ⟨E, hE, h⟩ => ⟨E, Finsupp.mem_support_iff.mpr hE, h⟩
  set K : ℤ := ∑ E ∈ Z₁.support, Z₁ E
  have hK : ∀ E, Z₁ E ≤ K := fun E => by
    by_cases hE : E ∈ Z₁.support
    · exact Finset.single_le_sum (f := ⇑Z₁) (fun E _ => hZ₁ E) hE
    · rw [Finsupp.notMem_support_iff.mp hE]
      exact Finset.sum_nonneg fun E _ => hZ₁ E
  set G : Divisor C := ∑ Q ∈ hT.toFinset, Finsupp.single Q K
  have hG : ∀ Q, G Q = if Q ∈ T then K else 0 := by
    intro Q
    simp only [G, Finset.sum_apply', Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun E _ => hZ₁ E
  have hG0 : 0 ≤ G := fun Q => by
    change (0 : ℤ) ≤ G Q
    rw [hG]; split_ifs <;> omega
  set G' := G.pullback (hcart G) (hη G) with hG'def
  have hG' : G.IsPullback p (hη G) G' := Divisor.isPullback_pullback (hcart G) (hη G)
  have hFpos : ∀ (Q : MMP.Mori.PrimeDivisor C) (E : MMP.Mori.PrimeDivisor X),
      p E.genericPoint = Q.genericPoint →
      0 < (Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)).coeff E :=
    fun Q E hE => MMP.Fourfold.coeff_pos_of_isPullback_single p Q
      (Divisor.isPullback_pullback (hcart _) (hη _)) E hE
  have hGZ : ∀ E, Z₁ E ≤ G' E := by
    intro E
    by_cases hE : Z₁ E = 0
    · rw [hE]
      exact (MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hG' E).1
        fun Q _ => hG0 Q
    · set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (p E.genericPoint)
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimC (hnotgen E hE))
      have hQ : Q.genericPoint = p E.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hQT : Q ∈ T := ⟨E, hE, hQ.symm⟩
      have h1 := coeff_isPullback_eq_mul hdimC p hη hcart hG' E Q hQ.symm
      have h2 := hFpos Q E hQ.symm
      rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hG, if_pos hQT] at h1
      rw [h1]
      have := hK E
      nlinarith
  -- `A = p^*G - Z₁` is effective, vertical, and `-A` is `p`-nef
  set A : QDivisor X := Divisor.toQDivisor G' - Divisor.toQDivisor Z₁ with hAdef
  have hAcoeff : ∀ E, A E = (G' E : ℚ) - (Z₁ E : ℚ) := fun E => by
    simp only [A, Finsupp.coe_sub, Pi.sub_apply]
    rw [toQDivisor_apply, toQDivisor_apply]
  have hA0 : 0 ≤ A := fun E => by
    change (0 : ℚ) ≤ A E
    rw [hAcoeff]
    have : ((Z₁ E : ℤ) : ℚ) ≤ (G' E : ℚ) := by exact_mod_cast hGZ E
    linarith
  have hAv : MMP.Fourfold.QDivisor.IsVertical p A := by
    intro E hE x hx
    by_cases hZ : Z₁ E = 0
    · have hG'E : G'.coeff E ≠ 0 := by
        intro h
        apply hE
        rw [hAcoeff, hZ, ← DivisorWithCoeffs.coeff_apply, h]
        simp
      by_contra hne'
      have hall : ∀ Q : MMP.Mori.PrimeDivisor C, p E.genericPoint = Q.genericPoint →
          G.coeff Q = 0 := by
        intro Q hQ
        exfalso
        apply hne'
        have hx' : E.genericPoint ⤳ x := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
          exact specializes_iff_mem_closure.mpr hx
        have h2 := hx'.map p.continuous
        rw [hQ] at h2
        have h3 := specializes_iff_mem_closure.mp h2
        rw [(isClosed_singleton_genericPoint hdimC Q).closure_eq] at h3
        rw [h3, hQ]
      exact hG'E ((MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hG' E).2 hall)
    · exact hvertpt E hZ x hx
  have hnef : (-A).IsRelativelyNef sX p := by
    have hAq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (-A)
    refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hAq
      fun γ hγ => ?_
    set R : Divisor X := principalDivisor ψ₁ - G'
    have hdecomp : -A = Divisor.toQDivisor D + Divisor.toQDivisor R := by
      rw [hAdef, hψ₁]
      simp only [R, map_add, map_sub]
      abel
    have hDq := QDivisor.isQCartier_toQDivisor hDc
    have hRq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (Divisor.toQDivisor R)
    rw [MMP.Fourfold.intersectionNumber_congr sX γ.ι γ.dim_le hAq (hDq.add hRq) hdecomp,
      QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ hDq hRq]
    have hloc : ∀ z : C, ∃ U : C.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
        R.IsLocalEquation (p ⁻¹ᵁ U) ψ := by
      intro z
      obtain ⟨U, hzU, φ, hφ⟩ := hcart G z
      obtain ⟨ψ, hψ, -⟩ := MMP.Fourfold.exists_isLocalEquation_of_isPullback p (hη G) hG' hφ
      refine ⟨U, hzU, ψ₁ * ψ⁻¹, fun E hE => ?_⟩
      rw [DivisorWithCoeffs.coeff_sub, hψ E hE, coeff_principalDivisor,
        MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_inv]
      ring
    have hR0 := MMP.Fourfold.intersectionNumber_eq_zero_of_isLocalEquation_preimage sX hQ p hRq
      (N := 1) one_pos (L := R) (by simp) hloc γ hγ
    rw [hR0, add_zero]
    obtain ⟨hL', hLn⟩ := hL
    have hLγ := hLn γ.scheme γ.ι γ.dim_eq
    have hDL' : Divisor.toQDivisor D = (m : ℚ) • L := by
      rw [hDL, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
    rw [MMP.Fourfold.intersectionNumber_congr sX γ.ι γ.dim_le hDq (hDL' ▸ hDq) hDL',
      MMP.Fourfold.intersectionNumber_smul sX γ.ι γ.dim_le L hL' (m : ℚ) (hDL' ▸ hDq)]
    exact mul_nonneg (by positivity) hLγ
  -- Zariski's lemma: `A = p^*P`
  have hCcurve : MMP.Mori.IsCurve k sC := (MMP.Mori.isCurve_iff k sC).mpr ⟨hC.toIsVariety, hdimC⟩
  obtain ⟨P, hP, hPB, -, hAP⟩ :=
    MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg sX sC hQ hX hCcurve
      hCsm p hpp hp A hA0 hAv hnef
  obtain ⟨N₀, hN₀, P₀, hP₀⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor P
  obtain ⟨D', hD', hD'pb⟩ := QDivisor.isPullback_pullback hP hPB N₀ hN₀ P₀ hP₀ (hcart P₀)
  -- `Z₁` is the pull-back of `B = N₀ G - P₀` divided by `N₀`
  set B : Divisor C := (N₀ : ℤ) • G + (-1 : ℤ) • P₀
  have hBpb0 : B.IsPullback p (hη B) ((N₀ : ℤ) • G' + (-1 : ℤ) • D') :=
    Divisor.IsPullback.add (hcart _) (hcart _) (hη _) (hG'.zsmul (hcart G) N₀ (hη _))
      (hD'pb.zsmul (hcart P₀) (-1) (hη _))
  have hBZ : (N₀ : ℤ) • G' + (-1 : ℤ) • D' = (N₀ : ℤ) • Z₁ := by
    apply Divisor.toQDivisor_injective
    rw [map_add, map_zsmul, map_zsmul, map_zsmul, hD', ← hAP, hAdef]
    simp only [smul_sub, neg_one_smul]
    abel
  have hBpb : B.IsPullback p (hη B) ((N₀ : ℤ) • Z₁) := hBZ ▸ hBpb0
  set n : ℕ := N₀ * m
  have hn : 0 < n := Nat.mul_pos hN₀ hm
  set N : QDivisor C := ((n : ℚ)⁻¹) • Divisor.toQDivisor B
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hNB : Divisor.toQDivisor B = (n : ℚ) • N := by
    simp only [N, smul_smul, mul_inv_cancel₀ hnq, one_smul]
  have hN : N.IsQCartier :=
    ⟨n, by exact_mod_cast hn.ne', B, by rw [hNB, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl,
      hcart B⟩
  have hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp := fun Z => by
    rw [hgenX]; exact MMP.Fourfold.genericPoint_notMem_supp N
  have hNpb : N.pullback hN hB = ((n : ℚ)⁻¹) • Divisor.toQDivisor ((N₀ : ℤ) • Z₁) :=
    QDivisor.IsPullback.pullback_eq hN (isPullback_smul_toQDivisor p hη hcart hBpb _ hB)
  -- `B` is effective and nonzero, hence ample
  have hB0 : 0 ≤ B := by
    intro Q
    change (0 : ℤ) ≤ B Q
    obtain ⟨E, hE⟩ := exists_primeDivisor_genericPoint_eq hdimC p hη hcart Q
    have h1 := coeff_isPullback_eq_mul hdimC p hη hcart hBpb E Q hE
    have h2 := hFpos Q E hE
    have h3 : (0 : ℤ) ≤ ((N₀ : ℤ) • Z₁).coeff E := by
      rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      exact mul_nonneg (by positivity) (hZ₁ E)
    rw [h1] at h3
    exact (mul_nonneg_iff_of_pos_right h2).mp h3
  have hBne : B ≠ 0 := by
    intro hB0'
    obtain ⟨E₀, hE₀⟩ := DFunLike.ne_iff.mp hne
    have hZE : Z₁ E₀ ≠ 0 := by
      intro h0
      apply hE₀
      have h1 := hF0 E₀
      have h2 : F E₀ ≤ Z₁ E₀ := (inf_le_left : F ≤ Z₁) E₀
      change Z₁ E₀ - F E₀ = 0
      change (0 : ℤ) ≤ F E₀ at h1
      omega
    have := (MMP.Fourfold.coeff_isPullback_nonneg_and_eq_zero hdimC p hη hcart hBpb E₀).2
      fun Q _ => by rw [hB0']; rfl
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact hZE h
  refine ⟨N, hN, n, hn, B, hNB, hcart B,
    isAmple_of_nonneg_of_ne_zero sC hC hdimC B (hcart B) hB0 hBne, hB, ?_⟩
  -- `L ∼_ℚ (1/m) Z₁ = p^*N`
  rw [hNpb]
  refine ⟨m, hm, ψ₁⁻¹, ?_⟩
  ext E
  have h1 := congrArg (fun G : QDivisor X => G.coeff E) hDL
  have h2 := congrArg (fun G : Divisor X => G.coeff E) hψ₁
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
    coeff_principalDivisor, MMP.Mori.PrimeDivisor.ord_inv, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, smul_eq_mul] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN₀q : (N₀ : ℚ) ≠ 0 := by exact_mod_cast hN₀.ne'
  simp only [n]
  push_cast
  field_simp
  rw [h2] at *
  push_cast
  rw [h1]
  ring

end Descent

/-- **The geometric part.** Under the assumptions of FA 15.4 with `ν(X, L) ≤ 1`, `L` is
`ℚ`-linearly equivalent to the pull-back of a `ℚ`-divisor with an ample Cartier multiple along a
morphism `p : X ⟶ C` onto a normal projective curve with `p_* 𝒪_X = 𝒪_C`. -/
private theorem exists_qLinearlyEquivalent_pullback {k : Type v} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hν : haveI := h.isProjectiveVariety
      haveI : IsProper sX := (inferInstance : AlgebraicGeometry.IsProperVariety k sX).toIsProper
      numericalDimension k sX inferInstance (Divisor.toQDivisor K + Δ) h.isNef ≤ 1) :
    ∃ (C : Scheme.{v}) (_ : IsLocallyNoetherian C) (_ : IsNormal C) (_ : CompactSpace C)
      (sC : C ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k sC)
      (_ : topologicalKrullDim C = 1) (p : X ⟶ C) (_ : p ≫ sC = sX)
      (_ : ∀ U : C.Opens, IsIso (p.app U)) (N : QDivisor C) (hN : N.IsQCartier)
      (n : ℕ) (_ : 0 < n) (A : Divisor C) (_ : Divisor.toQDivisor A = (n : ℚ) • N)
      (hAc : A.IsCartier) (_ : A.IsAmple hAc),
      ∃ hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp,
        (Divisor.toQDivisor K + Δ).QLinearlyEquivalent (N.pullback hN hB) := by
  classical
  have hXp := h.isProjectiveVariety
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  have hQ : MMP.Fourfold.IsQFactorial sX := h.isQFactorial
  obtain ⟨m, hm, D, hDL, hDc, h2⟩ := h.exists_two_le_h0
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, h12, h21⟩ := exists_sections_not_le hXp D h2
  set Z₁ := D.zeroDivisor σ₁ hσ₁ with hZ₁
  set Z₂ := D.zeroDivisor σ₂ hσ₂ with hZ₂
  set ψ₁ := (Divisor.isUnit_sectionToRationalFunctions hσ₁).unit
  set ψ₂ := (Divisor.isUnit_sectionToRationalFunctions hσ₂).unit
  have hψ₁ : Z₁ = principalDivisor ψ₁ + D := D.zeroDivisor_eq σ₁ hσ₁
  have hψ₂ : Z₂ = principalDivisor ψ₂ + D := D.zeroDivisor_eq σ₂ hσ₂
  have hψ : Z₂ = principalDivisor (ψ₂ * ψ₁⁻¹) + Z₁ := by
    rw [hψ₂, hψ₁, MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv]
    abel
  have hν2 : ∀ (x : X) (hV : topologicalKrullDim (curveSubschemeAt x) = 2) (E : Divisor X)
      (hE : E.IsCartier) (m' : ℕ), 0 < m' →
      Divisor.toQDivisor E = (m' : ℚ) • (Divisor.toQDivisor K + Δ) →
      Divisor.intersectionNumberOn k sX (curveSubschemeAtι x) 2 hV.le (fun _ => E)
        (fun _ => hE) = 0 := by
    intro x hV E hE m' hm' hEm
    by_contra hne
    have hmem : 2 ∈ numericalDimensionSet k sX (Divisor.toQDivisor K + Δ) := by
      refine Or.inr ⟨?_, x, hV, m', E, hE, hm', hEm, hne⟩
      rw [h.dim_eq]
      exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
    have hbdd : BddAbove (numericalDimensionSet k sX (Divisor.toQDivisor K + Δ)) := by
      refine ⟨3, fun d hd => ?_⟩
      rcases hd with rfl | ⟨hd, -⟩
      · norm_num
      · rw [h.dim_eq] at hd
        exact_mod_cast hd
    have h1 := le_csSup hbdd hmem
    have h2 : sSup (numericalDimensionSet k sX (Divisor.toQDivisor K + Δ)) ≤ 1 := hν
    omega
  have hZ₁0 : 0 ≤ Z₁ := D.zeroDivisor_nonneg σ₁ hσ₁
  have hZ₂0 : 0 ≤ Z₂ := D.zeroDivisor_nonneg σ₂ hσ₂
  obtain ⟨hdisj, hF⟩ := disjoint_of_intersection hXp h.dim_eq hQ h.isNef hm hDc hDL hν2 hZ₁0 hZ₂0
    ψ₁ ψ₂ hψ₁ hψ₂
  have hne₁ : Z₁ - Z₁ ⊓ Z₂ ≠ 0 := fun h0 => h12 (sub_eq_zero.mp h0 ▸ inf_le_right)
  have hne₂ : Z₂ - Z₁ ⊓ Z₂ ≠ 0 := fun h0 => h21 (sub_eq_zero.mp h0 ▸ inf_le_left)
  have hsupp : ∀ G : Divisor X, G ≠ 0 → ((G.supp : Set X)).Nonempty := by
    intro G hG
    obtain ⟨E, hE⟩ := DFunLike.ne_iff.mp hG
    refine ⟨E.genericPoint, DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, ?_⟩⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨hMc, τ₁, τ₂, hτ₁, hτ₂, hτ₁e, hτ₂e⟩ := exists_sections_of_disjoint hZ₁0 hZ₂0 _ hψ hdisj
  obtain ⟨C, _, _, _, sC, hC, hdimC, hCsm, p, hps, hp, hpsurj, hpp, hvert₁, hvert₂⟩ :=
    exists_curve_of_pencil hXp hMc τ₁ τ₂ hτ₁ hτ₂ (by rw [hτ₁e, hτ₂e]; exact hdisj)
    (by rw [hτ₁e]; exact hsupp _ hne₁) (by rw [hτ₂e]; exact hsupp _ hne₂)
  rw [hτ₁e] at hvert₁
  rw [hτ₂e] at hvert₂
  obtain ⟨N, hN, n, hn, A, hA, hAc, hAa, hB, hLN⟩ := exists_pullback_of_pencil hXp hQ h.isNef hm
    hDc hDL hZ₁0 hZ₂0 ψ₁ _ hψ₁ hψ hne₁ hdisj hF sC hC hdimC hCsm p hps hp hpp hvert₁ hvert₂
  exact ⟨C, inferInstance, inferInstance, inferInstance, sC, hC, hdimC, p, hps, hp, N, hN, n, hn,
    A, hA, hAc, hAa, hB, hLN⟩

end Proof_lem_fa15_nu_one_free_pencil

namespace MMP.Flips

universe u

open MMP.Mori

open Proof_lem_fa15_nu_one_free_pencil

/-- **FA 15.13.** Let `(X, Δ_X)` satisfy the assumptions of FA 15.4
(`MMP.Flips.SatisfiesAbundanceAssumptions`) and let `L = K_X + Δ_X`. If the numerical dimension
`ν(X, L)` (`MMP.Flips.numericalDimension`) is at most one, then `L` is eventually free and
composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`). -/
@[mmp "lem_fa15_nu_one_free_pencil"]
public theorem SatisfiesAbundanceAssumptions.isEventuallyFreePencil_of_numericalDimension_le_one
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (hν : haveI := h.isProjectiveVariety
      haveI : IsProper sX := (inferInstance : AlgebraicGeometry.IsProperVariety k sX).toIsProper
      numericalDimension k sX inferInstance (Divisor.toQDivisor K + Δ) h.isNef ≤ 1) :
    IsEventuallyFreePencil k sX (Divisor.toQDivisor K + Δ) := by
  obtain ⟨C, _, _, _, sC, hC, hdim, p, hps, hp, N, hN, n, hn, A, hA, hAc, hAa, hLN⟩ :=
    exists_qLinearlyEquivalent_pullback h hν
  exact (isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback k sX sC h.isProjectiveVariety
    hC p hps hp h.isQCartier hN hLN).mpr
    (isEventuallyFreePencil_of_isAmple_of_curve sC hC hdim N n hn A hA hAc hAa)

end MMP.Flips

namespace Proof_lem_fa18_procedure_log_resolution_exists

open TopologicalSpace MMP MMP.Mori MMP.Resolution

section Helpers

universe v

/-! ### Generalities on prime divisors -/

private theorem genericPoint_mem_support {X : Scheme.{v}} (P : Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{v}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{v}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{v}} (s : Finset (Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

private theorem coeff_sum_single {X : Scheme.{v}} (s : Finset (Mori.PrimeDivisor X))
    (P : Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The reduced divisor with components `s` has coefficients `0` and `1`. -/
private theorem coeff_sum_single_eq_zero_or_eq_one {X : Scheme.{v}}
    (s : Finset (Mori.PrimeDivisor X)) (P : Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 0 ∨
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 1 := by
  classical
  rw [coeff_sum_single]
  split_ifs <;> simp

/-- A coefficient of the linear extension of a partial map `φ` on prime divisors is nonzero only
at the image of a prime divisor with nonzero coefficient. -/
private theorem exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{v}}
    {R : Type*} [AddCommMonoid R] {φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {P : Mori.PrimeDivisor Y}
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Q with _ | E
  · rfl
  · have hne' : E ≠ P := fun he => hne Q (Finsupp.mem_support_iff.mp hQ) (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hne'

/-! ### Strict transforms under the inverse of a birational morphism -/

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{v}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing `f : Y ⟶ X` and `g'` a partial map representing
`e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{v}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{v}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint_mem_support P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    exact genericPoint_mem_support P

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{v}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{v}}
    [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_terminal_from {k : Type v} [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A component `P` of the strict transform `g⁻¹_* D` under a birational morphism of varieties
lies over a component `Q` of `D`: `g(η_P) = η_Q`. -/
private theorem exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero
    {k : Type v} [Field k] {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsVariety k sX) {g : Y ⟶ X} (hY : Mori.IsVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R X}
    {P : Mori.PrimeDivisor Y} (h : MMP.Flips.birationalInverseTransform g hg D P ≠ 0) :
    ∃ Q, D Q ≠ 0 ∧ g P.genericPoint = Q.genericPoint := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (g ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (g ≫ sX)
  obtain ⟨Q, hQ, hQP⟩ := exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero
    (φ := Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hg)) h
  exact ⟨Q, hQ, genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hg hQP⟩

/-! ### Prime divisors exceptional over `X` -/

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h) (by simp)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_injective h) (by simp)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = ((d + 2 : ℕ) : WithBot ℕ∞) by norm_cast]
        norm_cast
        omega

/-- A variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type v} [Field k] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) : ∃ n : ℕ, topologicalKrullDim X = n := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have h2 : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (IrreducibleCloseds X) := ⟨IrreducibleCloseds.closureSingleton x⟩
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff]
    exact not_isEmpty_of_nonempty _
  generalize topologicalKrullDim X = d at h1 h2
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- A prime divisor `P` of `Y` exceptional over `X` has its generic point in `Ex(f)`: over the
biregular locus of `f` the generic point of `P` goes to a point of coheight one. -/
private theorem genericPoint_mem_exceptionalSet {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{v}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y}
    (h : MMP.Flips.IsExceptionalPrimeDivisor sX f P) :
    P.genericPoint ∈ (exceptionalSet f : Set Y) := by
  obtain ⟨hY, hf, hp, hexc⟩ := h
  set D := MMP.Flips.ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp
  have h2 : 2 ≤ Order.coheight (f P.genericPoint) := by
    unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
    rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
      hn] at hexc
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f P.genericPoint)
    rw [hn] at h
    exact (withBot_add_two_le_iff h).mp hexc
  by_contra hmem
  have hV : f P.genericPoint ∈ biregularLocus f := by
    by_contra hV
    exact hmem (mem_exceptionalSet.mpr hV)
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hV, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-! ### Simple normal crossing closed subsets and their components -/

section SNC

variable {k : Type v} [Field k] {Y : Scheme.{v}} {sY : Y ⟶ Spec (.of k)}

private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hξ]; exact hle)
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (genericPoint_mem_support P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (genericPoint_mem_support P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => primeDivisor_eq_of_support_eq h
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (genericPoint_mem_support P)
      rw [hempty] at this
      exact this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (primeDivisor_eq_of_support_eq h1)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

/-- An snc reduced divisor in the sense of `DivisorWithCoeffs.IsSNC` is an snc divisor in the
sense of *Flips and abundance*. -/
private theorem isSNCDivisor_sum_single (s : Finset (Mori.PrimeDivisor Y))
    (h : (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY) :
    MMP.Flips.IsSNCDivisor sY (∑ P ∈ s, Finsupp.single P (1 : ℤ)) := by
  classical
  refine ⟨coeff_sum_single_eq_zero_or_eq_one s, h.1, fun p _ => ?_⟩
  · obtain ⟨n, z, j, hz, hj, hI⟩ := h.2 p
    exact ⟨n, z, j, hz, hj, hI⟩

end SNC

/-! ### From an snc closed subset to a log resolution -/

/-- **A resolution with snc exceptional set and inverse image of the boundary is a log
resolution.** Let `X` be a normal variety over a field of characteristic zero, `B` a boundary on
`X` and `g : Y ⟶ X` a resolution such that `Ex(g) ∪ g⁻¹(Supp B)` is a divisor with simple normal
crossings. Then `g` is a log resolution of `(X, B)`: the components of `g⁻¹_* B` and the prime
divisors exceptional over `X` lie in `Ex(g) ∪ g⁻¹(Supp B)`, so the reduced divisor they form is
snc. -/
private theorem isLogResolution_of_isSNCClosedSubset {k : Type v} [Field k] {X Y : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} {B : RDivisor X} (hB : MMP.Flips.IsLogVariety k sX B) {g : Y ⟶ X}
    (hres : IsResolutionOfVariety sX g)
    (hS : IsSNCClosedSubset (g ≫ sX) ((exceptionalSet g : Set Y) ∪ g ⁻¹' (B.supp : Set X))) :
    MMP.Flips.IsLogResolution sX B g := by
  classical
  have hX : IsNormalVariety k sX := hB.isNormalVariety
  have hYv : Mori.IsVariety k (g ≫ sX) := hres.isVariety_source
  have hg : IsBirationalMorphism g := hres.isBirationalMorphism
  have hsm : IsSmoothScheme (g ≫ sX) := hres.isSmoothScheme
  have : IsProper g := hres.isProjective.isProper
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (g ≫ sX) := hYv.toQuasiCompact
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq sX hX.1
  set S : Set Y := (exceptionalSet g : Set Y) ∪ g ⁻¹' (B.supp : Set X) with hSdef
  have hsub : ∀ P : Mori.PrimeDivisor Y,
      (MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) → (P.support : Set Y) ⊆ S := by
    intro P hP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hS.1
    rcases hP with hP | hP
    · obtain ⟨Q, hQ, hgQ⟩ :=
        exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero hX.1 hYv hg hP
      right
      change g P.genericPoint ∈ (B.supp : Set X)
      rw [hgQ]
      exact DivisorWithCoeffs.support_subset_supp hQ (genericPoint_mem_support Q)
    · left
      exact genericPoint_mem_exceptionalSet hn hP
  have hfin : {P : Mori.PrimeDivisor Y |
      MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P}.Finite :=
    (finite_setOf_support_subset hS).subset fun P hP => hsub P hP
  set s := hfin.toFinset with hs
  have hG := isSNC_sum_single_of_support_subset hsm hS s
    (fun P hP => hsub P (by simpa [hs] using hP))
  refine ⟨hB, hYv, hsm, inferInstance, hg, ∑ P ∈ s, Finsupp.single P (1 : ℤ),
    coeff_sum_single_eq_zero_or_eq_one s, fun P => ?_, isSNCDivisor_sum_single s hG⟩
  · rw [coeff_sum_single]
    have hmem : P ∈ s ↔ (MMP.Flips.birationalInverseTransform g hg B P ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX g P) := by
      rw [hs, Set.Finite.mem_toFinset]
      rfl
    split_ifs with h
    · exact ⟨fun _ => hmem.mp h, fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd (hmem.mpr h') h⟩

/-! ### Simple normal crossings at a regular point -/

/-- In a regular local ring, a regular quotient by a prime of height one is the quotient by one
element of a regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_eq_span {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (I : Ideal R) [I.IsPrime] (hI : I.height = 1)
    (hq : IsRegularLocalRing (R ⧸ I)) :
    ∃ (n : ℕ) (w : Fin n → R) (c : Fin n), IsRegularSystemOfParameters w ∧
      I = Ideal.span {w c} := by
  obtain ⟨k, h, hspan, hdim⟩ :=
    MMP.Flips.ResolutionInputs.exists_fin_span_eq_of_isRegularLocalRing_quotient I hq
  have h1 := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one I hI
  have hN : ((IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (R ⧸ I) := IsRegularLocalRing.spanFinrank_maximalIdeal
  have hk : k = 1 := by
    rw [← hN] at hdim h1
    have := hdim.trans h1.symm
    have : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank + k =
        (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank + 1 := by exact_mod_cast this
    omega
  subst hk
  obtain ⟨m, t, hz⟩ :=
    (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff h).1
      ⟨hspan ▸ hq, hspan ▸ hdim⟩
  refine ⟨1 + m, Fin.append h t, Fin.castAdd m 0, hz, ?_⟩
  rw [← hspan, Fin.append_left]
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rw [Subsingleton.elim i 0]
  · rintro rfl
    exact ⟨0, rfl⟩

/-- **The support of a divisor is snc at a regular point where it is smooth.** If the local ring
of `Z` at `z` is regular, and, when `z ∈ Supp D`, so is its quotient by the ideal of `Supp D`,
then `Supp D` is a simple normal crossing divisor at `z`: the ideal of `Supp D` at `z` is the
height-one prime of the one component through `z`, generated by one regular parameter. -/
private theorem isSNCAt_supp {Z : Scheme.{v}} [IsLocallyNoetherian Z] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R Z) (z : Z) (hreg : IsRegularLocalRing (Z.presheaf.stalk z))
    (hq : z ∈ D.supp →
      IsRegularLocalRing (Z.presheaf.stalk z ⧸ IdealSheafData.stalk D.suppIdeal z)) :
    IsSNCAt (D.supp : Set Z) z := by
  classical
  by_cases hz : z ∈ D.supp
  · have hreg' := hq hz
    set I := IdealSheafData.stalk D.suppIdeal z with hIdef
    have : IsDomain (Z.presheaf.stalk z ⧸ I) := IsRegularLocalRing.isDomain _
    have hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
    have hinf := MMP.Intersection.stalk_suppIdeal D z
    obtain ⟨E, hE, hEI⟩ := (hIp.inf_le').mp (le_of_eq hinf.symm)
    have hIE : I = IdealSheafData.stalk E.idealSheaf z :=
      le_antisymm (by rw [hIdef, hinf]; exact Finset.inf_le hE) hEI
    have : (IdealSheafData.stalk E.idealSheaf z).IsPrime := hIE ▸ hIp
    have hht : (IdealSheafData.stalk E.idealSheaf z).height = 1 :=
      MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne E.idealSheaf
        (isPureCodimOne_support_primeDivisor E)
    have : I.IsPrime := hIp
    obtain ⟨n, w, c, hw, hwc⟩ :=
      exists_isRegularSystemOfParameters_eq_span I (hIE ▸ hht) hreg'
    refine ⟨n, w, {c}, hw, ?_⟩
    rw [← DivisorWithCoeffs.coe_support_suppIdeal, preimage_fromSpecStalk_support, ← hIdef, hwc,
      PrimeSpectrum.zeroLocus_span]
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    rfl
  · obtain ⟨n, w, hw⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Z.presheaf.stalk z)
    refine ⟨n, w, ∅, hw, ?_⟩
    have hempty : Z.fromSpecStalk z ⁻¹' (D.supp : Set Z) = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp => by
        have hsp : Z.fromSpecStalk z p ⤳ z := by
          have : Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z) := ⟨p, rfl⟩
          rwa [Scheme.range_fromSpecStalk] at this
        exact hz (hsp.mem_closed D.supp.isClosed hp)
    rw [hempty]
    ext p
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_iUnion,
      exists_false, iff_false]
    exact Iff.rfl

/-- Being snc at a point is invariant under morphisms inducing an isomorphism of local rings. -/
private theorem isSNCAt_preimage_of_isIso_stalkMap {X Y : Scheme.{v}} (ψ : Y ⟶ X) {T : Set X}
    {y : Y} [IsIso (ψ.stalkMap y)] (h : IsSNCAt T (ψ y)) : IsSNCAt (ψ ⁻¹' T) y := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  exact ⟨n, fun i => (ψ.stalkMap y).hom (w i), C,
    isRegularSystemOfParameters_map_ringEquiv
      (asIso (ψ.stalkMap y)).commRingCatIsoToRingEquiv hw,
    preimage_fromSpecStalk_preimage ψ y hT⟩

/-- **Pulling back a divisor with smooth support on a regular scheme.** Let `φ : U ⟶ Z` be an
open immersion into a locally noetherian scheme, `U` of finite type over a perfect field, such
that `Z` is regular at every point of the image and `Supp D` is regular at every point of the
image it contains. Then `φ⁻¹(Supp D)` is an snc closed subset of `U`. -/
private theorem isSNCClosedSubset_preimage_supp {k : Type v} [Field k] [PerfectField k]
    {U Z : Scheme.{v}} (sU : U ⟶ Spec (.of k)) [LocallyOfFiniteType sU] [CompactSpace U]
    [IsLocallyNoetherian Z] (φ : U ⟶ Z) [IsOpenImmersion φ] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R Z) (hreg : ∀ u, IsRegularLocalRing (Z.presheaf.stalk (φ u)))
    (hq : ∀ u, φ u ∈ D.supp →
      IsRegularLocalRing (Z.presheaf.stalk (φ u) ⧸ IdealSheafData.stalk D.suppIdeal (φ u))) :
    IsSNCClosedSubset sU (φ ⁻¹' (D.supp : Set Z)) :=
  isSNCClosedSubset_of_forall_isSNCAt sU (D.supp.isClosed.preimage φ.continuous) fun u =>
    have : IsIso (φ.stalkMap u) := inferInstanceAs (IsIso (φ.toLRSHom.stalkMap u))
    isSNCAt_preimage_of_isIso_stalkMap φ (isSNCAt_supp D (φ u) (hreg u) (hq u))

/-- Over a perfect field, a scheme is smooth when all its local rings are regular. -/
private theorem isSmoothScheme_of_forall_isRegularLocalRing {k : Type v} [Field k]
    [PerfectField k] {Y : Scheme.{v}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme s := by
  have : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr inferInstance
  rw [isSmoothScheme_iff]
  exact (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk s).mpr h

/-! ### The contraction over the complement of `Supp H'` -/

/-- A birational contraction `f : Y ⟶ X` to a normal variety is an isomorphism over every open
`V ⊆ X` with `f⁻¹(V) ∩ Ex(f) = ∅`: the fibres over `V` are finite. -/
private theorem le_biregularLocus_of_forall_notMem {k : Type v} [Field k] {X Y : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsNormal X] {f : Y ⟶ X}
    (hf : MMP.Flips.IsBirationalContraction k sX sY f) {V : X.Opens}
    (hV : ∀ y, f y ∈ V → y ∉ MMP.Flips.exceptionalSet f) : V ≤ biregularLocus f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have := hf.isProper
  have := hf.isVariety_target.toLocallyOfFiniteType
  have := hf.isVariety_target.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have hbir : AlgebraicGeometry.IsBirational f :=
    MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      hf.surjective_and_isBirational.2
  intro x hx
  have hfib : ∀ y ∈ f ⁻¹' {x}, y ∉ MMP.Flips.exceptionalSet f := fun y hy =>
    hV y (by rw [show f y = x from hy]; exact hx)
  have hfin : (f ⁻¹' {x}).Finite := by
    have hcpt : IsCompact (f ⁻¹' {x}) :=
      f.isProperMap.isCompact_preimage isCompact_singleton
    have hU : ∀ y ∈ f ⁻¹' {x}, ∃ U : Y.Opens, y ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
      fun y hy => MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet (hfib y hy)
    choose! U hyU hU using hU
    obtain ⟨t, hts, hcov⟩ := hcpt.elim_nhds_subcover (fun y => (U y : Set Y))
      (fun y hy => (U y).isOpen.mem_nhds (hyU y hy))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.mp (hcov hz)
    have hy := hts y hyt
    have := hU y hy
    have hzy' : (⟨z, hzy⟩ : (U y).toScheme) = ⟨y, hyU y hy⟩ :=
      ((U y).ι ≫ f).isOpenEmbedding.injective (hz.trans hy.symm)
    have := congrArg Subtype.val hzy'
    simp only at this
    rw [this]
    exact hyt
  have := IsNormal.stalk_normal (X := X) x
  obtain ⟨U, hxU, hUiso⟩ := exists_isIso_restrict_of_finite_fiber_of_normal f hbir x hfin
  exact le_biregularLocus hUiso hxU

/-- Over an open `V` with `f ∣_ V` an isomorphism, `f⁻¹(V) ⟶ X ⟶ Z` is an open immersion. -/
private theorem isOpenImmersion_ι_comp {X Z : Scheme.{v}} (f : X ⟶ Z) {V : Z.Opens}
    (h : IsIso (f ∣_ V)) : IsOpenImmersion ((f ⁻¹ᵁ V).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  infer_instance

/-- **The supports agree over the biregular locus.** Let `f : X ⟶ Z` be a proper birational
morphism of normal varieties, an isomorphism over `V`. For `x ∈ f⁻¹(V)`, `x` lies on a component
of `D` exactly when `f(x)` lies on a component of `f_* D`. -/
private theorem mem_supp_iff_map_mem_supp_transformDivisor {k : Type v} [Field k]
    {X Z : Scheme.{v}} {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace X] [CompactSpace Z]
    (hZ : IsNormalVariety k sZ) {f : X ⟶ Z} (hX : IsNormalVariety k (f ≫ sZ)) [IsProper f]
    (hf : IsBirationalMorphism f) {V : Z.Opens} (hV : IsIso (f ∣_ V)) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {x : X} (hx : f x ∈ V) :
    x ∈ D.supp ↔ f x ∈ (Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D).supp := by
  have hV' : V ≤ biregularLocus f := isBiregular_iff_le_biregularLocus.mp hV
  have hoi := isOpenImmersion_ι_comp f hV
  set φ := (f ⁻¹ᵁ V).ι ≫ f
  have hinj : ∀ a b : X, f a ∈ V → f b ∈ V → f a = f b → a = b := fun a b ha hb hab =>
    congrArg Subtype.val (φ.isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hspec : ∀ a b : X, f a ∈ V → f b ∈ V → f a ⤳ f b → a ⤳ b := fun a b ha hb hab => by
    have := (φ.isOpenEmbedding.isInducing.specializes_iff (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)).mp hab
    exact this.map (f ⁻¹ᵁ V).ι.continuous
  rw [DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨E, hE, hxE⟩
    have hηx : E.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
      exact specializes_iff_mem_closure.mpr hxE
    have hηV : f E.genericPoint ∈ V := (hηx.map f.continuous).mem_open V.isOpen hx
    have hco : Order.coheight (f E.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f (hV' hηV), E.coheight_genericPoint]
    set Q : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hQ : Q.genericPoint = f E.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    obtain ⟨E', hE'Q, -, hcoeff⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hf Q
    have hE'E : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hinj _ _ (by rwa [hE'Q, hQ]) hηV (hE'Q.trans hQ))
    refine ⟨Q, ?_, ?_⟩
    · rwa [DivisorWithCoeffs.coeff_apply, hcoeff, hE'E]
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change f x ∈ closure {Q.genericPoint}
      rw [hQ]
      exact specializes_iff_mem_closure.mp (hηx.map f.continuous)
  · rintro ⟨Q, hQ, hxQ⟩
    obtain ⟨E, hEQ, -, hcoeff⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hf Q
    have hηx : Q.genericPoint ⤳ f x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxQ
      exact specializes_iff_mem_closure.mpr hxQ
    have hηV : f E.genericPoint ∈ V := by rw [hEQ]; exact hηx.mem_open V.isOpen hx
    refine ⟨E, ?_, ?_⟩
    · rwa [DivisorWithCoeffs.coeff_apply, ← hcoeff]
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp (hspec _ _ hηV hx (by rwa [hEQ]))

end Helpers

end Proof_lem_fa18_procedure_log_resolution_exists

namespace MMP.Flips

open MMP.Mori

open Proof_lem_fa18_procedure_log_resolution_exists TopologicalSpace MMP MMP.Resolution

/-- **A log resolution adapted to a procedure datum** (FA 18.12.2). Let `X` be a normal variety
over a field `k` of characteristic zero, `D` a boundary on `X`, `f : X ⟶ Z` a small projective
contraction to a quasi-projective variety `Z`, `P` a procedure datum for `(X, D, f)` with divisor
`H'`, and `H = f^*H'`. Then there is a projective log resolution `g : Y ⟶ X` of
`(X, D ⊔ Supp H)` such that `g ≫ f` is an isomorphism over `Z ∖ Supp H'`. -/
@[mmp "lem_fa18_procedure_log_resolution_exists"]
public theorem ProcedureDatum.exists_isLogResolution_isIso_restrict.{u}
    {k : Type u} [Field k] [CharZero k] {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Z] [IsNormal Z] [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (hD : IsLogVariety k sX D) {f : X ⟶ Z}
    (hf : IsSmall k sZ sX f) (hfp : IsProjectiveMorphism f)
    (hZ : IsQuasiProjectiveVariety k sZ) (P : ProcedureDatum k sZ D f)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ P.H'.supp}
    {H : Divisor X} (hH : P.H'.IsPullback f hB H) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsLogResolution sX (D ⊔ Divisor.toRDivisor (Intersection.reducedDivisorOf H.support)) g ∧
        IsProjectiveMorphism g ∧ IsIso ((g ≫ f) ∣_ P.H'.supp.compl) := by
  classical
  set B : RDivisor X := D ⊔ Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf H.support)
  have hX : IsNormalVariety k sX := hD.isNormalVariety
  have hZv : Mori.IsVariety k sZ := hf.isVariety_target
  have hZn : IsNormalVariety k sZ := ⟨hZv, inferInstance⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Z := hZv.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : QuasiCompact sZ := hZv.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian X := ⟨⟩
  have : IsProper f := hf.isProper
  have hcomp : f ≫ sZ = sX := hf.comp_eq
  have hfbir : IsBirationalMorphism f := hf.surjective_and_isBirational.2
  -- the coefficients of `B`
  have hHe : MMP.Mori.DivisorWithCoeffs.IsEffective P.H' := fun E => by
    rcases P.isReduced_H' E with h | h <;> simp [h]
  have hHsupp : (H.supp : Set X) = f.base ⁻¹' (P.H'.supp : Set Z) :=
    MMP.Flips.supp_eq_preimage_supp_of_isPullback P.isCartier_H' hHe hH
  have hred : ∀ E, (Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf H.support)).coeff E =
      if E ∈ H.support then 1 else 0 := fun E => by
    rw [Divisor.coeff_toRDivisor, MMP.Intersection.coeff_reducedDivisorOf]
    split_ifs <;> simp
  have hBcoeff : ∀ E, B.coeff E = max (D.coeff E)
      ((Divisor.toRDivisor (MMP.Intersection.reducedDivisorOf H.support)).coeff E) := fun E => rfl
  have hBb : MMP.Flips.IsLogVariety k sX B := by
    refine ⟨hX, fun E => ?_⟩
    obtain ⟨h0, h1⟩ := hD.isBoundary E
    rw [hBcoeff, hred]
    split_ifs
    · exact ⟨le_max_of_le_left h0, max_le h1 le_rfl⟩
    · exact ⟨le_max_of_le_left h0, max_le h1 zero_le_one⟩
  -- the snc-preserving log resolution of `(X, Supp B)`
  obtain ⟨Y, g, hres, -, hS, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  have hsupp_eq : (B.supp : Set X) = B.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  -- `X` is quasi-projective over `k`, so the EGA-projective `g` is H-projective
  have hXqp : IsQuasiProjective sX := hcomp ▸
    IsQuasiProjective.comp f sZ (isQuasiProjective_of_isProjective hfp.isProjective)
      hZ.isQuasiProjective
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, _, hLa⟩ := exists_isAmple_of_isQuasiProjective sX _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) hXqp
  refine ⟨Y, g, isLogResolution_of_isSNCClosedSubset hBb hres hS,
    isProjectiveMorphism_of_isProjective g L hLa hres.isProjective, ?_⟩
  -- `f` is an isomorphism over `V = Z ∖ Supp H'`
  set V : Z.Opens := P.H'.supp.compl
  have hVb : V ≤ biregularLocus f :=
    le_biregularLocus_of_forall_notMem hf.toIsBirationalContraction fun y hyV hyE =>
      hyV (P.exceptionalSet_subset hyE)
  have hfV : IsIso (f ∣_ V) := isBiregular_iff_le_biregularLocus.mpr hVb
  set U : X.Opens := f ⁻¹ᵁ V
  have hoi : IsOpenImmersion (U.ι ≫ f) := isOpenImmersion_ι_comp f hfV
  set φ : U.toScheme ⟶ Z := U.ι ≫ f
  have hφV : ∀ u : U.toScheme, φ u ∈ V := fun u => u.2
  have hregZ : ∀ z ∈ V, IsRegularLocalRing (Z.presheaf.stalk z) := fun z hz => by
    by_contra h
    exact hz (P.nonregular_subset z h)
  have hφst : ∀ u : U.toScheme, IsIso (φ.stalkMap u) := fun u =>
    inferInstanceAs (IsIso (φ.toLRSHom.stalkMap u))
  have hregU : ∀ u : U.toScheme, IsRegularLocalRing (U.toScheme.presheaf.stalk u) := fun u => by
    have := hregZ _ (hφV u)
    have := hφst u
    exact IsRegularLocalRing.of_ringEquiv (asIso (φ.stalkMap u)).commRingCatIsoToRingEquiv
  have : LocallyOfFiniteType (U.ι ≫ sX) := inferInstance
  have hUsm : IsSmoothScheme (U.ι ≫ sX) := isSmoothScheme_of_forall_isRegularLocalRing _ hregU
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact U.1)
  -- `Supp B ∩ U` is `φ⁻¹(Supp f_* D)`
  have heq : U.ι ⁻¹' (B.supp : Set X) =
      φ ⁻¹' ((MMP.Flips.divisorPushforward f D).supp : Set Z) := by
    ext u
    have hxV : f u.1 ∈ V := u.2
    have hxH : u.1 ∉ (H.supp : Set X) := by rw [hHsupp]; exact hxV
    have hXn' : IsNormalVariety k (f ≫ sZ) := by rw [hcomp]; exact hX
    change u.1 ∈ B.supp ↔ f u.1 ∈ (MMP.Flips.divisorPushforward f D).supp
    rw [← mem_supp_iff_map_mem_supp_transformDivisor hZn hXn' hfbir hfV D hxV,
      DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.mem_supp_iff]
    refine exists_congr fun E => and_congr_left fun hxE => ?_
    have hEH : E ∉ H.support := fun hEH =>
      hxH (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hEH) hxE)
    rw [hBcoeff, hred, if_neg hEH, max_eq_left (hD.isBoundary E).1]
  have hUsnc : IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (B.supp : Set X)) := by
    rw [heq]
    exact isSNCClosedSubset_preimage_supp _ φ _ (fun u => hregZ _ (hφV u)) fun u hz => by
      by_contra h
      exact hφV u (P.nonregular_supp_subset _ hz h)
  have hgU : IsIso (g ∣_ U) := hiso U hUsm (by rw [← hsupp_eq]; exact hUsnc)
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hgU hfV

end MMP.Flips
