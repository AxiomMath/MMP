module

public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TelescopeProjectiveSpace

/-!
# Free pencils under crepant morphisms, and blowing up a point of a surface resolution

Two results from the study of surface germs and abundance.

**Free pencils.** Let `p : X ⟶ Y` be a morphism of normal projective varieties over a field `k`
with `p_* 𝒪_X = 𝒪_Y`, and let `L` on `X` and `N` on `Y` be `ℚ`-Cartier `ℚ`-divisors with
`L ∼_ℚ p^* N`. Then `L` is eventually free and composed of a pencil if and only if `N` is. After
clearing denominators this reduces to three facts about a Cartier divisor `M`: if `|M|` is
composed of a free pencil then so is `|nM|` for `n > 0`; the property depends only on the linear
equivalence class of `M`; and for `M` Cartier on `Y`, `|p^* M|` is composed of a free pencil if
and only if `|M|` is.

**Blowing up a point.** Let `g : Y ⟶ X` be a resolution of a surface germ `(X, P)` over an
algebraically closed field, with exceptional curves `E_1, …, E_n` and log discrepancy vector `a`
of `(X, P; B)`, let `y ∈ g⁻¹(P)` be a closed point, `π : Y' ⟶ Y` the blow-up of `y` and
`F = π⁻¹(y)_red`. Then `g ∘ π` is a resolution of `(X, P)` whose exceptional curves are the
birational transforms `E'_j = π⁻¹_* E_j` together with `F`, and its log discrepancy vector `a'`
is given by `a'_{E'_j} = a_j` and `a'_F = 2 - mult_y Θ_{g,a}`, where
`Θ_{g,a} = g⁻¹_* B + ∑_j (1 - a_j) E_j`.

## Main definitions

* `MMP.Flips.pullbackDivisorialSectionsEquiv`: for `p_* 𝒪_X = 𝒪_Y` and a Cartier divisor `B` on
  `Y`, the pull-back of sections `H⁰(Y, 𝒪_Y(B)) ≃ H⁰(X, 𝒪_X(p^* B))`.

## Main results

* `MMP.Flips.isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback`.
* `MMP.Flips.linearSystemLocus_map_of_pullback`: the open of a pulled-back linear system is the
  preimage of the open of the original one.
* `MMP.Flips.topologicalKrullDim_linearSystemImage_map_of_pullback`: under a surjective
  pull-back, the image of a free linear system keeps its dimension.
* `MMP.Flips.topologicalKrullDim_linearSystemImage_eq_of_isPullback`: for `p_* 𝒪_X = 𝒪_Y`, the
  image of `|p^* B|` has the dimension of the image of `|B|` when `|B|` is free.
* `MMP.Flips.isGermLogDiscrepancyVector_snoc_blowUp_iff`.

## Implementation notes

The condition `p_* 𝒪_X = 𝒪_Y` is `∀ U, IsIso (p.app U)`. The pull-back `p^* N` is
`MMP.Mori.QDivisor.pullback`, which takes as argument that `p` maps the generic point of `X`
outside `Supp N`; the crepancy hypothesis asserts this together with `L ∼_ℚ p^* N` (it holds
automatically, `p` being surjective).

The blow-up is `AlgebraicGeometry.blowUp` of the reduced closed point `y`, and `F` is the prime
divisor of `Y'` whose ideal sheaf is `AlgebraicGeometry.exceptionalIdeal`. The exceptional curves
of `g ∘ π` are enumerated as `Fin.snoc E' F`, with `F` last, and the log discrepancy vector as
`Fin.snoc a (2 - mult_y Θ_{g,a})`. That `a'` *is* the log discrepancy vector is stated as the
equivalence "`a'` is a log discrepancy vector of `(X, P; B)` on `g ∘ π` iff
`a' = (a, 2 - mult_y Θ_{g,a})`", which contains both its existence and its uniqueness. It is
`MMP.Flips.isGermLogDiscrepancyVector_snoc_blowUp_iff_of_isCanonicalDivisor` with its canonical
divisor hypothesis discharged by
`MMP.Threefold.Resolution.isCanonicalDivisor_pullback_add_single_blowUp_singleton`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.4, 3.1.5,
  3.3.2, 15.7.1, 15.9
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

section FreePencil

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

private theorem toProjectiveSpaceAtUniverse_eq_of_iso {X : Scheme.{u}} {n : ℕ} {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L']
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    (s' : Fin (n + 1) → Γ(L', ⊤)) (hs' : GeneratesStalks s') (β : L ≅ L')
    (h : ∀ i, β.hom.app ⊤ (s i) = s' i) :
    toProjectiveSpaceAtUniverse s hs = toProjectiveSpaceAtUniverse s' hs' := by
  let t : GeneratingTuple X n := ⟨L, ‹_›, s, hs⟩
  let t' : GeneratingTuple X n := ⟨L', ‹_›, s', hs'⟩
  have hp : IsPinned t (toProjectiveSpaceAtUniverse s hs) :=
    fun i => ι_toProjectiveSpaceAtUniverse s hs i
  have hp' : IsPinned t' (toProjectiveSpaceAtUniverse s' hs') :=
    fun i => ι_toProjectiveSpaceAtUniverse s' hs' i
  exact eq_of_isPinned (isPinned_of_isomorphic (t := t) (t' := t') ⟨β, h⟩ hp) hp'

/-- Dimension of the closure of the range of a map. -/
private noncomputable def rdim {A B : Type*} [TopologicalSpace B] (f : A → B) : WithBot ℕ∞ :=
  topologicalKrullDim (closure (Set.range f))

private theorem rdim_comp_surjective {A A' B : Type*} [TopologicalSpace B] (f : A → B) {h : A' → A}
    (hh : Function.Surjective h) : rdim (f ∘ h) = rdim f := by
  unfold rdim; rw [hh.range_comp]

private theorem rdim_homeomorph_comp {A B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    (f : A → B) (e : B ≃ₜ C) : rdim (e ∘ f) = rdim f := by
  unfold rdim
  rw [Set.range_comp, ← e.image_closure]
  exact ((e.image _).isHomeomorph.topologicalKrullDim_eq).symm

private theorem finiteDimensional_globalSections (k : Type u) [Field k] {X : Scheme.{u}}
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
    have h := Module.Finite.equiv e
    exact h
  refine key _ ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ sX.appTop).hom = _
  rw [hEq]

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

private theorem topologicalKrullDim_linearSystemImage (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
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
private theorem linearSystemMap_comp_basisIso (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
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

private theorem topologicalKrullDim_linearSystemImage_eq (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
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

private theorem generatesStalks_of_linearSystemLocus_eq_top (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (e : Fin (n + 1) ≃ ι)
    (htop : linearSystemLocus k L b = ⊤) : GeneratesStalks (fun i => b (e i)) :=
  Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => by
    obtain ⟨j, hj⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
    exact ⟨e.symm j, show x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L (b (e (e.symm j))) by
      rw [Equiv.apply_symm_apply]; exact hj⟩

private theorem toProjectiveSpaceOver_eq_of_iso {X S : Scheme.{u}} {n : ℕ} {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L']
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    (s' : Fin (n + 1) → Γ(L', ⊤)) (hs' : GeneratesStalks s') (β : L ≅ L')
    (h : ∀ i, β.hom.app ⊤ (s i) = s' i) (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f = toProjectiveSpaceOver s' hs' f := by
  unfold toProjectiveSpaceOver
  rw [toProjectiveSpaceAtUniverse_eq_of_iso s hs s' hs' β h]

/-- A basis of the finite-dimensional sections of an invertible sheaf on a nonempty scheme whose
linear-system locus is everything is indexed by a type equivalent to some `Fin (n + 1)`. -/
private theorem exists_equiv_fin_of_linearSystemLocus_eq_top (k : Type u) [Field k] {X : Scheme.{u}}
    [Nonempty X] [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    {ι : Type u} (b : Module.Basis ι k Γ(L, ⊤)) [FiniteDimensional k Γ(L, ⊤)]
    (htop : linearSystemLocus k L b = ⊤) : ∃ n : ℕ, Nonempty (Fin (n + 1) ≃ ι) := by
  haveI : Finite ι := Module.Finite.finite_basis b
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j, -⟩ := (mem_linearSystemLocus_iff k L b x).1 (htop ▸ trivial)
  cases m with
  | zero => exact (e j).elim0
  | succ n => exact ⟨n, ⟨e.symm⟩⟩

private theorem isComposedOfFreePencil_add_principalDivisor (k : Type u) [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) {M : Divisor X} (h : IsComposedOfFreePencil k sX M)
    (φ : (RationalFunctions X)ˣ) :
    IsComposedOfFreePencil k sX (M + principalDivisor φ) := by
  obtain ⟨hX, hM, ι, b, hloc, hdim⟩ := h
  have hM' : (M + principalDivisor φ).IsCartier := hM.add (Divisor.isCartier_principalDivisor φ)
  refine ⟨hX, hM', ?_⟩
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI := hM.isInvertibleModule_divisorialSheaf
  haveI := hM'.isInvertibleModule_divisorialSheaf
  haveI := hX.toIsIntegral
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have hle : (M + principalDivisor φ).LinearlyEquivalent M := ⟨φ, by abel⟩
  let E : M.divisorialSheaf ≅ (M + principalDivisor φ).divisorialSheaf :=
    hle.divisorialSheafIso.symm
  let b' := b.map (globalSectionsLinearEquiv k E)
  have hloc' : linearSystemLocus k _ b' = ⊤ := (linearSystemLocus_map_iso k _ b E).trans hloc
  refine ⟨ι, b', hloc', ?_⟩
  haveI := finiteDimensional_globalSections k sX M.divisorialSheaf
  obtain ⟨n, ⟨e⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ b hloc
  rw [topologicalKrullDim_linearSystemImage_eq k _ b e
    (generatesStalks_of_linearSystemLocus_eq_top k _ b e hloc) hloc] at hdim
  rw [topologicalKrullDim_linearSystemImage_eq k _ b' e
    (generatesStalks_of_linearSystemLocus_eq_top k _ b' e hloc') hloc', ← hdim,
    toProjectiveSpaceOver_eq_of_iso _ (generatesStalks_of_linearSystemLocus_eq_top k _ b e hloc)
      (fun i => b' (e i)) (generatesStalks_of_linearSystemLocus_eq_top k _ b' e hloc') E
      (fun i => by simp [b'])]

private theorem comp_toProjectiveSpaceOver' {X Y S : Scheme.{u}} (h : X ⟶ Y) {n : ℕ} {L : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y L]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback h).obj L)]
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    (hs' : GeneratesStalks (fun i => pullbackGlobalSections h L (s i))) (f : Y ⟶ S) :
    h ≫ toProjectiveSpaceOver s hs f =
      toProjectiveSpaceOver (fun i => pullbackGlobalSections h L (s i)) hs' (h ≫ f) := by
  refine CategoryTheory.Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, toProjectiveSpaceOver_fst, toProjectiveSpaceOver_fst]
  · rw [Category.assoc, toProjectiveSpaceOver_snd, toProjectiveSpaceOver_snd,
      comp_toProjectiveSpaceAtUniverse _ _ _ hs']

/-- For `p : X ⟶ Y`, an invertible sheaf `ℱ` on `Y`, an isomorphism `E : ℱ' ≅ p^* ℱ` and a
`k`-linear `Q : H⁰(Y, ℱ) ≃ H⁰(X, ℱ')` carrying a section to its pull-back, the open of the linear
system of the basis `Q b` of `H⁰(X, ℱ')` is the preimage of the open of the linear system of
`b`. -/
theorem linearSystemLocus_map_of_pullback (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (p : X ⟶ Y)
    (F : Y.Modules) [Stacks.Ample.IsInvertibleModule Y F] (F' : X.Modules)
    [Stacks.Ample.IsInvertibleModule X F']
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback p).obj F)]
    (E : F' ≅ (Scheme.Modules.pullback p).obj F) (Q : Γ(F, ⊤) ≃ₗ[k] Γ(F', ⊤))
    (hQ : ∀ s, E.hom.app ⊤ (Q s) = pullbackGlobalSections p F s)
    {ι : Type u} (b : Module.Basis ι k Γ(F, ⊤)) :
    linearSystemLocus k F' (b.map Q) = p ⁻¹ᵁ linearSystemLocus k F b := by
  rw [← linearSystemLocus_map_iso k F' (b.map Q) E]
  exact linearSystemLocus_pullback k p F b _ fun i => by simp [hQ]

/-- **The image of a linear system does not change under a surjective pull-back.** Let
`p : X ⟶ Y` be a surjective morphism over `k`, `ℱ` an invertible sheaf on `Y` with
finite-dimensional `H⁰(Y, ℱ)`, `E : ℱ' ≅ p^* ℱ` and `Q : H⁰(Y, ℱ) ≃ H⁰(X, ℱ')` carrying a section
to its pull-back. If the basis `b` of `H⁰(Y, ℱ)` generates `ℱ` everywhere, the images of the
linear systems of `Q b` and of `b` have the same dimension. -/
theorem topologicalKrullDim_linearSystemImage_map_of_pullback (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Nonempty Y] (p : X ⟶ Y)
    (hps : p ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)) (hsurj : Function.Surjective p.base)
    (F : Y.Modules) [Stacks.Ample.IsInvertibleModule Y F] [FiniteDimensional k Γ(F, ⊤)]
    (F' : X.Modules) [Stacks.Ample.IsInvertibleModule X F']
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback p).obj F)]
    (E : F' ≅ (Scheme.Modules.pullback p).obj F) (Q : Γ(F, ⊤) ≃ₗ[k] Γ(F', ⊤))
    (hQ : ∀ s, E.hom.app ⊤ (Q s) = pullbackGlobalSections p F s)
    {ι : Type u} (b : Module.Basis ι k Γ(F, ⊤)) (htop : linearSystemLocus k F b = ⊤) :
    topologicalKrullDim (linearSystemImage k F' (b.map Q)) =
      topologicalKrullDim (linearSystemImage k F b) := by
  have htop' : linearSystemLocus k F' (b.map Q) = ⊤ := by
    rw [linearSystemLocus_map_of_pullback k p F F' E Q hQ b, htop]; rfl
  obtain ⟨n, ⟨e⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k F b htop
  have hg := generatesStalks_of_linearSystemLocus_eq_top k F b e htop
  have hg' := generatesStalks_of_linearSystemLocus_eq_top k F' (b.map Q) e htop'
  have hgp : GeneratesStalks (fun i => pullbackGlobalSections p F (b (e i))) :=
    (pullbackTuple p ⟨F, ‹_›, _, hg⟩).generates
  rw [topologicalKrullDim_linearSystemImage_eq k F b e hg htop,
    topologicalKrullDim_linearSystemImage_eq k F' (b.map Q) e hg' htop',
    toProjectiveSpaceOver_eq_of_iso _ hg' _ hgp E (fun i => by simp [hQ]), ← hps,
    ← comp_toProjectiveSpaceOver' p _ hg hgp]
  exact rdim_comp_surjective
    (⇑(toProjectiveSpaceOver (fun i => b (e i)) hg (Y ↘ Spec (.of k))).base)
    (h := ⇑p.base) hsurj

section PullbackSections

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (p : X ⟶ Y)
  (hps : p ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)) (hp : ∀ U : Y.Opens, IsIso (p.app U))
  {B : Divisor Y} (hBc : B.IsCartier)
  {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ B.supp}
  {B' : Divisor X} (hpb : B.IsPullback p hB B')

/-- **Pulling back sections of a Cartier divisor along a morphism with `p_* 𝒪_X = 𝒪_Y`.** For
`p : X ⟶ Y` over `k` with `p_* 𝒪_X = 𝒪_Y` and a Cartier divisor `B` on `Y` with pull-back `B'`,
the `k`-linear isomorphism `H⁰(Y, 𝒪_Y(B)) ≃ H⁰(X, 𝒪_X(B'))`: pull-back of sections
`H⁰(Y, 𝒪_Y(B)) ≃ H⁰(X, p^* 𝒪_Y(B))`, followed by `𝒪_X(B') ≅ p^* 𝒪_Y(B)`
(`MMP.Mori.Divisor.IsPullback.divisorialSheafIso`). -/
noncomputable def pullbackDivisorialSectionsEquiv :
    Γ(B.divisorialSheaf, ⊤) ≃ₗ[k] Γ(B'.divisorialSheaf, ⊤) :=
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI : IsIso p.c := NatIso.isIso_of_isIso_app _
  haveI := Scheme.Modules.isIso_unit_app_of_isIso_c p B.divisorialSheaf
  (LinearEquiv.ofBijective
    (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ k p
      B.divisorialSheaf hps)
    (Stacks.Algebraization.bijective_pullbackGlobalSections_of_isIso_unit p
      B.divisorialSheaf)).trans
    (globalSectionsLinearEquiv k (hpb.divisorialSheafIso (hBc := hBc))).symm

/-- `pullbackDivisorialSectionsEquiv` carries a section of `𝒪_Y(B)` to its pull-back, read
through `𝒪_X(B') ≅ p^* 𝒪_Y(B)`. -/
@[simp]
theorem divisorialSheafIso_hom_app_pullbackDivisorialSectionsEquiv
    (s : Γ(B.divisorialSheaf, ⊤)) :
    (hpb.divisorialSheafIso (hBc := hBc)).hom.app ⊤
        (pullbackDivisorialSectionsEquiv k p hps hp hBc hpb s) =
      pullbackGlobalSections p B.divisorialSheaf s :=
  (globalSectionsLinearEquiv k (hpb.divisorialSheafIso (hBc := hBc))).apply_symm_apply
    (pullbackGlobalSections p B.divisorialSheaf s)

/-- **The image of `|B|` does not change under a pull-back with `p_* 𝒪_X = 𝒪_Y`.** Let
`p : X ⟶ Y` be a morphism of proper schemes over `k` with `p_* 𝒪_X = 𝒪_Y`, `X` integral, and `B`
a Cartier divisor on `Y` with pull-back `B'`. If the basis `b` of `H⁰(Y, 𝒪_Y(B))` generates
`𝒪_Y(B)` everywhere, then the images of `φ_{|B'|}` for the transported basis and of `φ_{|B|}` for
`b` have the same dimension. -/
theorem topologicalKrullDim_linearSystemImage_eq_of_isPullback
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [Stacks.Ample.IsInvertibleModule Y B.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X B'.divisorialSheaf]
    {ι : Type u} (b : Module.Basis ι k Γ(B.divisorialSheaf, ⊤))
    (htop : linearSystemLocus k B.divisorialSheaf b = ⊤) :
    topologicalKrullDim (linearSystemImage k B'.divisorialSheaf
        (b.map (pullbackDivisorialSectionsEquiv k p hps hp hBc hpb))) =
      topologicalKrullDim (linearSystemImage k B.divisorialSheaf b) := by
  haveI : IsProper (p ≫ (Y ↘ Spec (.of k))) := hps ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p (Y ↘ Spec (.of k))
  haveI : Stacks.Ample.IsInvertibleModule X
      ((Scheme.Modules.pullback p).obj B.divisorialSheaf) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p _
  have : FiniteDimensional k Γ(B.divisorialSheaf, ⊤) :=
    finiteDimensional_globalSections k (Y ↘ Spec (.of k)) B.divisorialSheaf
  haveI : Nonempty Y := ⟨p (Nonempty.some inferInstance)⟩
  exact topologicalKrullDim_linearSystemImage_map_of_pullback k p hps
    (p.surjective_of_isIso_app hp).surj _ _ _ _
    (divisorialSheafIso_hom_app_pullbackDivisorialSectionsEquiv k p hps hp hBc hpb) b htop

end PullbackSections

private theorem isComposedOfFreePencil_iff_of_isPullback (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    (p : X ⟶ Y) (hps : p ≫ sY = sX) (hp : ∀ U : Y.Opens, IsIso (p.app U))
    {B : Divisor Y} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (hpb : B.IsPullback p hB B') :
    IsComposedOfFreePencil k sX B' ↔ IsComposedOfFreePencil k sY B := by
  haveI := hX.toIsIntegral
  haveI := hY.toIsIntegral
  haveI : CompactSpace Y := by
    haveI := hY.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sY
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : IsProper (Y ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism sY hY.isProjective
  haveI : IsProper (p ≫ sY) := hps ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p sY
  have hsurj : Function.Surjective p.base := (p.surjective_of_isIso_app hp).surj
  have hB'c : B'.IsCartier := hpb.isCartier hBc
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback p).obj B.divisorialSheaf) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p _
  have hps' : p ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k) := hps
  let Q := pullbackDivisorialSectionsEquiv k p hps' hp hBc hpb
  have hQ := divisorialSheafIso_hom_app_pullbackDivisorialSectionsEquiv k p hps' hp hBc hpb
  constructor
  · rintro ⟨_, _, ι, c, hloc, hdim⟩
    have hc : (c.map Q.symm).map Q = c := by ext i; simp
    have hlocY : linearSystemLocus k _ (c.map Q.symm) = ⊤ := by
      have h1 := linearSystemLocus_map_of_pullback k p _ _ _ Q hQ (c.map Q.symm)
      rw [hc, hloc] at h1
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨x, rfl⟩ := hsurj y
      exact (h1 ▸ trivial : x ∈ p ⁻¹ᵁ linearSystemLocus k _ (c.map Q.symm))
    refine ⟨hY, hBc, ι, c.map Q.symm, hlocY, ?_⟩
    rwa [← topologicalKrullDim_linearSystemImage_eq_of_isPullback k p hps' hp hBc hpb _ hlocY, hc]
  · rintro ⟨_, _, ι, b, hloc, hdim⟩
    have hloc' : linearSystemLocus k _ (b.map Q) = ⊤ := by
      rw [linearSystemLocus_map_of_pullback k p _ _ _ Q hQ b, hloc]; rfl
    refine ⟨hX, hB'c, ι, b.map Q, hloc', ?_⟩
    rwa [topologicalKrullDim_linearSystemImage_eq_of_isPullback k p hps' hp hBc hpb _ hloc]

/-! ### Dimension of images -/

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

/-- An irreducible T0 space of dimension at most zero is a point. -/
private theorem subsingleton_of_topologicalKrullDim_le_zero {S : Type*} [TopologicalSpace S]
    [IrreducibleSpace S] [T0Space S] (h : topologicalKrullDim S ≤ 0) :
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
  refine ⟨fun p q => ?_⟩
  have hp : IsGenericPoint p Set.univ := key p
  have hq : IsGenericPoint q Set.univ := key q
  exact hp.eq hq

private theorem eq_one_of_le_one_of_not_le_zero {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) :
    d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      have h1' : m ≤ 1 := by exact_mod_cast h1
      have h0' : ¬ m ≤ 0 := fun h => h0 (by exact_mod_cast h)
      obtain rfl : m = 1 := by omega
      rfl

/-! ### Sections of divisorial sheaves read on local equations -/

/-- The rational function underlying a section of `𝒪_X(D)`. -/
private def secVal {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W : X.Opens} (m : D.divisorialSheaf.val.obj (Opposite.op W)) :
    ToType ((rationalFunctionsPresheaf X).obj (Opposite.op W)) :=
  (show D.divisorialSubmodule W from m).1

private theorem secVal_map {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W W' : X.Opens} (h : W' ⟶ W) (m : D.divisorialSheaf.val.obj (Opposite.op W)) (Z) :
    secVal (D.divisorialSheaf.val.map h.op m) Z = secVal m ⟨Z.1, h.le Z.2⟩ := rfl

private theorem secVal_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X}
    {W : X.Opens} (r : X.ringCatSheaf.obj.obj (Opposite.op W))
    (m : D.divisorialSheaf.val.obj (Opposite.op W)) (Z) :
    secVal (r • m) Z = X.presheaf.germ W _ Z.2 r * secVal m Z := rfl

private theorem secVal_injective {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {W : X.Opens} :
    Function.Injective (secVal (D := D) (W := W)) := fun _ _ h => Subtype.ext h

/-- The local generator `ψ⁻¹` of `𝒪_X(D)` over an open on which `ψ` is a local equation. -/
private noncomputable def localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) : D.divisorialSheaf.val.obj (Opposite.op U) :=
  (⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E hE => Or.inr (by
    rw [E.valuation_component, PrimeDivisor.ord_inv, hψ E hE])⟩ : D.divisorialSubmodule U)

private theorem secVal_localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) (Z) :
    secVal (localGen hψ) Z = ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := rfl

private theorem bijective_smul_localGen {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U) :
    Function.Bijective (fun r : X.ringCatSheaf.obj.obj (Opposite.op W) =>
      r • D.divisorialSheaf.val.map h.op (localGen hψ)) := by
  refine ⟨fun r r' hrr => ?_, fun m => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective W
    funext Z
    have := congrFun (congrArg secVal hrr) Z
    have hu : IsUnit (((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1) :=
      ⟨RationalFunctions.unitsEquiv X ψ⁻¹ Z.1, rfl⟩
    exact hu.mul_left_injective this
  · let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op W)) :=
      fun Z => (ψ : RationalFunctions X) Z.1 * secVal m Z
    have hφ : (0 : Divisor X).IsDivisorialSection W φ := by
      intro E hE
      have h1 : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
        Or.inr (E.valuation_component ψ).ge
      have h2 := (show D.divisorialSubmodule W from m).2 E hE
      have h3 := h1.mul h2
      refine h3.mono (le_of_eq ?_)
      rw [hψ E (hE.mono (Set.inter_subset_inter_right _ h.le)),
        DivisorWithCoeffs.coeff_zero]
      ring
    obtain ⟨a, ha⟩ := Divisor.IsDivisorialSection.exists_eq hφ
    refine ⟨a, secVal_injective (funext fun Z => ?_)⟩
    have hZ := congrFun ha Z
    rw [toRationalFunctionsPresheaf_app_apply] at hZ
    refine (secVal_smul (D := D) (W := W) a _ Z).trans ?_
    rw [secVal_map, secVal_localGen, hZ]
    simp only [φ]
    rw [mul_comm, ← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Pi.one_apply, one_mul]

/-- The coordinate of a section of `𝒪_X(D)` with respect to the local generator. -/
private noncomputable def localCoord {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U) :
    (D.divisorialSheaf.val.obj (Opposite.op W) : Type u) ≃ₗ[
      (X.ringCatSheaf.obj.obj (Opposite.op W) : Type u)]
      (X.ringCatSheaf.obj.obj (Opposite.op W) : Type u) :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).symm

private theorem eq_localCoord_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U)
    (m : D.divisorialSheaf.val.obj (Opposite.op W)) :
    m = localCoord hψ h m • D.divisorialSheaf.val.map h.op (localGen hψ) :=
  ((LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).apply_symm_apply m).symm

private theorem localCoord_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) {W : X.Opens} (h : W ⟶ U)
    (r : X.ringCatSheaf.obj.obj (Opposite.op W)) :
    localCoord hψ h (r • D.divisorialSheaf.val.map h.op (localGen hψ)) = r :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (D.divisorialSheaf.val.map h.op (localGen hψ)))
    (bijective_smul_localGen hψ h)).symm_apply_apply r

/-- The sectionwise trivialization of `𝒪_X(D)` over an open carrying a local equation. -/
private noncomputable def localTriv {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) :
    Stacks.SheafDescent.Trivialization X.presheaf D.divisorialSheaf.val U where
  θ W h := localCoord hψ h
  θ_naturality {W W'} h h' m := by
    have key : D.divisorialSheaf.val.map h'.op m =
        X.ringCatSheaf.obj.map h'.op (localCoord hψ h m) •
          D.divisorialSheaf.val.map (h' ≫ h).op (localGen hψ) := by
      refine (congrArg (D.divisorialSheaf.val.map h'.op) (eq_localCoord_smul hψ h m)).trans ?_
      refine (PresheafOfModules.map_smul D.divisorialSheaf.val h'.op _ _).trans ?_
      congr 1
    exact (congrArg (localCoord hψ (h' ≫ h)) key).trans (localCoord_smul _ _ _)

/-- **Nonvanishing of a section of `𝒪_X(D)` read on a local equation.** If `ψ` is a local equation
of `D` on `U` and `a` is the regular function `ψ σ` on `U`, then `σ` does not vanish at `y ∈ U`
exactly when `a` is a unit at `y`. -/
private theorem mem_nonvanishingLocus_iff_isUnit_germ {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation U ψ)
    (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) (a : Γ(X, U))
    (ha : ∀ Z, X.presheaf.germ U _ Z.2 a = (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z)
    {y : X} (hy : y ∈ U) :
    y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf σ ↔
      IsUnit (X.presheaf.germ U y hy a) := by
  rw [Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit (localTriv hψ) σ hy]
  suffices h : Stacks.NonvanishingOpen.trivTop (localTriv hψ) σ = a by rw [h]
  change localCoord hψ (𝟙 U) (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) = a
  apply (bijective_smul_localGen hψ (𝟙 U)).1
  refine secVal_injective (funext fun Z => ?_)
  refine (congrFun (congrArg secVal (eq_localCoord_smul hψ (𝟙 U) _).symm) Z).trans ?_
  refine Eq.trans ?_ (show X.presheaf.germ U _ Z.2 a *
    ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 = _ from rfl)
  rw [ha, mul_comm, ← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Pi.one_apply, one_mul]

/-- On an open carrying a local equation `ψ` of `D`, the product `ψ σ` of a global section of
`𝒪_X(D)` is a regular function. -/
private theorem exists_germ_eq_mul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U ψ) (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) :
    ∃ a : Γ(X, U), ∀ Z, X.presheaf.germ U _ Z.2 a = (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z := by
  let φ : ToType ((rationalFunctionsPresheaf X).obj (Opposite.op U)) := fun Z =>
    (ψ : RationalFunctions X) Z.1 *
      secVal (D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ) Z
  have hφ : (0 : Divisor X).IsDivisorialSection U φ := by
    intro E hE
    have h1 : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions X) E.component) :=
      Or.inr (E.valuation_component ψ).ge
    have h2 := (show D.divisorialSubmodule U from
      D.divisorialSheaf.val.map (homOfLE (le_top : U ≤ ⊤)).op σ).2 E hE
    refine (h1.mul h2).mono (le_of_eq ?_)
    rw [hψ E hE, DivisorWithCoeffs.coeff_zero]
    ring
  obtain ⟨a, ha⟩ := Divisor.IsDivisorialSection.exists_eq hφ
  exact ⟨a, fun Z => (toRationalFunctionsPresheaf_app_apply a Z).symm.trans (congrFun ha Z)⟩

/-- The `n`-th power `σⁿ` of a global section `σ` of `𝒪_X(D)`, a global section of `𝒪_X(nD)`. -/
private noncomputable def powSection {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) (n : ℕ) :
    (n • D).divisorialSheaf.val.obj (Opposite.op ⊤) :=
  (⟨fun Z => secVal σ Z ^ n, fun E hE =>
    (((show D.divisorialSubmodule ⊤ from σ).2 E hE).pow n).mono (le_of_eq (by
      simp [DivisorWithCoeffs.coeff_smul]))⟩ : (n • D).divisorialSubmodule ⊤)

/-- **`σⁿ` vanishes exactly where `σ` does**, for a Cartier divisor `D` and `n ≠ 0`. -/
private theorem nonvanishingLocus_powSection {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} (hD : D.IsCartier)
    (σ : D.divisorialSheaf.val.obj (Opposite.op ⊤)) {n : ℕ} (hn : n ≠ 0) :
    Stacks.Ample.nonvanishingLocus (n • D).divisorialSheaf (powSection σ n) =
      Stacks.Ample.nonvanishingLocus D.divisorialSheaf σ := by
  ext y
  obtain ⟨U, hyU, ψ, hψ⟩ := hD y
  have hψn : (n • D).IsLocalEquation U (ψ ^ n) := fun E hE => by
    rw [PrimeDivisor.ord_pow, ← hψ E hE]
    simp [DivisorWithCoeffs.coeff_smul]
  obtain ⟨a, ha⟩ := exists_germ_eq_mul hψ σ
  have han : ∀ Z, X.presheaf.germ U _ Z.2 (a ^ n) = ((ψ ^ n : (RationalFunctions X)ˣ) :
      RationalFunctions X) Z.1 * secVal ((n • D).divisorialSheaf.val.map
        (homOfLE (le_top : U ≤ ⊤)).op (powSection σ n)) Z := by
    intro Z
    rw [map_pow, ha Z, Units.val_pow_eq_pow_val, Pi.pow_apply, mul_pow]
    rfl
  rw [mem_nonvanishingLocus_iff_isUnit_germ hψn _ _ han hyU,
    mem_nonvanishingLocus_iff_isUnit_germ hψ _ _ ha hyU, map_pow, isUnit_pow_iff hn]

/-! ### Morphisms to projective space with a point as image -/

/-- A morphism from a scheme whose global functions form a field to an affine scheme has at most
one point in its image. -/
private theorem subsingleton_range_of_isAffine {Z W : Scheme.{u}} [IsAffine W]
    (hZ : IsField Γ(Z, ⊤)) (f : Z ⟶ W) : (Set.range f.base).Subsingleton := by
  rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
  have hs : Z.toSpecΓ z₁ = Z.toSpecΓ z₂ :=
    @Subsingleton.elim (PrimeSpectrum Γ(Z, ⊤)) (by letI := hZ.toField; infer_instance) _ _
  have e : ∀ z, W.toSpecΓ (f z) = Spec.map f.appTop (Z.toSpecΓ z) := fun z => by
    rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]
  have h1 : W.toSpecΓ (f z₁) = W.toSpecΓ (f z₂) := by rw [e, e, hs]
  exact (Scheme.homeoOfIso (asIso W.toSpecΓ)).injective h1

/-- If one of the sections `sⱼ` vanishes nowhere, the morphism `φ_s` to `ℙⁿ_S`, `S` affine,
factors through the affine standard chart `D₊(Tⱼ)`; when the global functions of the source form a
field, its image is a single point. -/
private theorem subsingleton_range_toProjectiveSpaceOver_of_nonvanishing {Z S : Scheme.{u}}
    [IsAffine S] (hZ : IsField Γ(Z, ⊤)) {n : ℕ} {L : Z.Modules}
    [Stacks.Ample.IsInvertibleModule Z L] (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    (f : Z ⟶ S) (j : Fin (n + 1))
    (hj : ∀ z, z ∈ Stacks.Ample.nonvanishingLocus L (s j)) :
    (Set.range (toProjectiveSpaceOver s hs f).base).Subsingleton := by
  have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart s hs
    (toProjectiveSpaceOver s hs f) (fun i => ι_toProjectiveSpaceOver s hs f i) j
  have : IsAffine (projectiveSpaceOver.standardChart n S j).toScheme :=
    .of_isIso (projectiveSpaceOver.standardChartIso n j (Equiv.ulift.{u} (α := {i // i ≠ j})) S).inv
  have hrange : Set.range (toProjectiveSpaceOver s hs f).base ⊆
      Set.range (projectiveSpaceOver.standardChart n S j).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : z ∈ (toProjectiveSpaceOver s hs f) ⁻¹ᵁ projectiveSpaceOver.standardChart n S j := by
      rw [hpre]
      exact hj z
    exact this
  let g := IsOpenImmersion.lift (projectiveSpaceOver.standardChart n S j).ι
    (toProjectiveSpaceOver s hs f) hrange
  have hg : g ≫ (projectiveSpaceOver.standardChart n S j).ι = toProjectiveSpaceOver s hs f :=
    IsOpenImmersion.lift_fac _ _ _
  rw [← hg]
  rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    subsingleton_range_of_isAffine hZ g ⟨z₁, rfl⟩ ⟨z₂, rfl⟩]

/-- If the image of `φ_s` is a point, some `sⱼ` vanishes nowhere. -/
private theorem exists_forall_mem_nonvanishingLocus_of_subsingleton {Z S : Scheme.{u}}
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
    rw [h ⟨z, rfl⟩ ⟨z₀, rfl⟩]
    exact h0
  rwa [hpre] at hz

private theorem isClosedMap_toProjectiveSpaceOver {Z S : Scheme.{u}} (f : Z ⟶ S) [IsProper f]
    {n : ℕ} {L : Z.Modules} [Stacks.Ample.IsInvertibleModule Z L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) : IsClosedMap (toProjectiveSpaceOver s hs f).base := by
  have : IsProper (toProjectiveSpaceOver s hs f ≫ CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
    rw [toProjectiveSpaceOver_fst]
    infer_instance
  have := IsProper.of_comp (toProjectiveSpaceOver s hs f) (CategoryTheory.Limits.pullback.fst
      (CategoryTheory.Limits.terminal.from S)
      (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{u} n)))
  exact (toProjectiveSpaceOver s hs f).isClosedMap

/-- A basis of the sections of an invertible sheaf generating it at every point gives the whole
space as the open of the linear system. -/
private theorem linearSystemLocus_eq_top_of_forall (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {ι : Type u}
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

/-- **The image of `φ_{|nD|}` is not a point if that of `φ_{|D|}` is not**, for a Cartier
divisor `D`, `n ≠ 0`, and sections `s` of `𝒪(D)` with `s 0 ≠ 0`. -/
private theorem not_subsingleton_range_toProjectiveSpaceOver_nsmul (k : Type u) [Field k]
    {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Z] (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] {D : Divisor Z} (hD : D.IsCartier) {n : ℕ} (hn : n ≠ 0)
    [Stacks.Ample.IsInvertibleModule Z D.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule Z (n • D).divisorialSheaf]
    {m : ℕ} (s : Fin (m + 1) → Γ(D.divisorialSheaf, ⊤)) (hs : GeneratesStalks s) (hs0 : s 0 ≠ 0)
    (hφ : ¬ (Set.range (toProjectiveSpaceOver s hs sZ).base).Subsingleton)
    {m' : ℕ} (t : Fin (m' + 1) → Γ((n • D).divisorialSheaf, ⊤)) (ht : GeneratesStalks t) :
    ¬ (Set.range (toProjectiveSpaceOver t ht sZ).base).Subsingleton := by
  intro hψ
  have hZ : IsField Γ(Z, ⊤) := Stacks.Models.isField_globalSections_of_connectedSpace k sZ
  obtain ⟨j, hj⟩ := exists_forall_mem_nonvanishingLocus_of_subsingleton t ht sZ hψ
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul Z (n • D).divisorialSheaf (t j)
    (W := ⊤) (fun z _ => hj z)).2 (powSection (s 0) n)
  have hres : (n • D).divisorialSheaf.presheaf.map (homOfLE (le_refl (⊤ : Z.Opens))).op (t j) =
      t j := by
    rw [show homOfLE (le_refl (⊤ : Z.Opens)) = 𝟙 ⊤ from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  simp only [hres] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    apply hs0
    refine secVal_injective (funext fun Z' => ?_)
    have := congrFun (congrArg secVal ha.symm) Z'
    exact IsReduced.eq_zero (secVal (s 0) Z') ⟨n, this⟩
  obtain ⟨a', ha'⟩ := hZ.mul_inv_cancel ha0
  have hu : IsUnit a := IsUnit.of_mul_eq_one a' ha'
  have hall : ∀ z, z ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf (s 0) := by
    intro z
    rw [← nonvanishingLocus_powSection hD (s 0) hn, ← ha, Stacks.Ample.nonvanishingLocus_smul]
    refine ⟨?_, hj z⟩
    rw [Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hφ (subsingleton_range_toProjectiveSpaceOver_of_nonvanishing hZ s hs sZ 0 hall)

/-- **Free pencils on a scheme of dimension at most one.** If `|D|` is composed of a free pencil
on a normal projective variety `Z` of dimension at most one, so is `|nD|` for `n > 0`. -/
private theorem isComposedOfFreePencil_nsmul_of_topologicalKrullDim_le_one (k : Type u)
    [Field k] {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z] (sZ : Z ⟶ Spec (.of k))
    {D : Divisor Z} (h : IsComposedOfFreePencil k sZ D) (hZ1 : topologicalKrullDim Z ≤ 1)
    {n : ℕ} (hn : 0 < n) : IsComposedOfFreePencil k sZ (n • D) := by
  obtain ⟨hZ, hD, ι, b, hloc, hdim⟩ := h
  have := hZ.toIsIntegral
  have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ.isProjective
  have : CompactSpace Z := by
    have := hZ.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sZ
  letI : Z.Over (Spec (.of k)) := ⟨sZ⟩
  have hnD := hD.nsmul n
  have := hD.isInvertibleModule_divisorialSheaf
  have := hnD.isInvertibleModule_divisorialSheaf
  have := finiteDimensional_globalSections k sZ D.divisorialSheaf
  have := finiteDimensional_globalSections k sZ (n • D).divisorialSheaf
  let c := Module.Basis.ofVectorSpace k Γ((n • D).divisorialSheaf, ⊤)
  have hlocc : linearSystemLocus k _ c = ⊤ := by
    refine linearSystemLocus_eq_top_of_forall k _ c fun x => ?_
    obtain ⟨i, hi⟩ := (mem_linearSystemLocus_iff k _ b x).1 (hloc ▸ trivial)
    exact ⟨powSection (b i) n,
      (Set.ext_iff.1 (nonvanishingLocus_powSection hD (b i) hn.ne') x).2 hi⟩
  refine ⟨hZ, hnD, _, c, hlocc, ?_⟩
  obtain ⟨m, ⟨e⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ b hloc
  obtain ⟨m', ⟨e'⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ c hlocc
  have hg := generatesStalks_of_linearSystemLocus_eq_top k _ b e hloc
  have hg' := generatesStalks_of_linearSystemLocus_eq_top k _ c e' hlocc
  rw [topologicalKrullDim_linearSystemImage_eq k _ b e hg hloc] at hdim
  rw [topologicalKrullDim_linearSystemImage_eq k _ c e' hg' hlocc]
  have hφc := isClosedMap_toProjectiveSpaceOver sZ (fun i => b (e i)) hg
  have hψc := isClosedMap_toProjectiveSpaceOver sZ (fun i => c (e' i)) hg'
  unfold rdim at hdim ⊢
  change topologicalKrullDim (closure (Set.range
    (toProjectiveSpaceOver (fun i => b (e i)) hg sZ).base)) = 1 at hdim
  change topologicalKrullDim (closure (Set.range
    (toProjectiveSpaceOver (fun i => c (e' i)) hg' sZ).base)) = 1
  rw [hφc.isClosed_range.closure_eq] at hdim
  rw [hψc.isClosed_range.closure_eq]
  have hφns : ¬ (Set.range (toProjectiveSpaceOver (fun i => b (e i)) hg sZ).base).Subsingleton := by
    intro hsub
    have := (Set.subsingleton_coe _).2 hsub
    have := topologicalKrullDim_zero_of_discreteTopology
      (Set.range (toProjectiveSpaceOver (fun i => b (e i)) hg sZ).base)
    rw [hdim] at this
    exact absurd this (by decide)
  have hψns := not_subsingleton_range_toProjectiveSpaceOver_nsmul k sZ hD hn.ne'
    (fun i => b (e i)) hg (b.ne_zero (e 0)) hφns (fun i => c (e' i)) hg'
  refine eq_one_of_le_one_of_not_le_zero ?_ fun h0 => hψns ?_
  · exact (topologicalKrullDim_range_le_of_isClosedMap _
      (toProjectiveSpaceOver (fun i => c (e' i)) hg' sZ).continuous hψc).trans hZ1
  · have : IrreducibleSpace
        (Set.range (toProjectiveSpaceOver (fun i => c (e' i)) hg' sZ).base) := by
      refine Subtype.irreducibleSpace ?_
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Z).image _
        (toProjectiveSpaceOver (fun i => c (e' i)) hg' sZ).continuous.continuousOn
    exact (Set.subsingleton_coe _).1 (subsingleton_of_topologicalKrullDim_le_zero h0)

/-! ### The Stein factorization of `φ_{|M|}` -/

/-- Two points of a fibre of a finite morphism, one specializing to the other, are equal. -/
private theorem eq_of_specializes_of_isFinite' {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g]
    {a b : Y'} (hab : a ⤳ b) (hg : g a = g b) : a = b := by
  have hd := g.isDiscrete_preimage_singleton (g b)
  have : DiscreteTopology (g ⁻¹' {g b}) := hd.to_subtype
  have hs : (⟨a, hg⟩ : g ⁻¹' {g b}) ⤳ ⟨b, rfl⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hab
  have := hs.mem_open (isOpen_discrete {⟨b, rfl⟩}) rfl
  exact congrArg Subtype.val this

/-- A finite morphism does not lower the dimension of its source below that of its image. -/
private theorem topologicalKrullDim_le_rdim_of_isFinite {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    [IsFinite g] : topologicalKrullDim Y' ≤ rdim g.base := by
  unfold rdim
  refine topologicalKrullDim_le_of_specializes_imp_eq
    (f := fun y => (⟨g y, subset_closure ⟨y, rfl⟩⟩ : closure (Set.range g.base)))
    (g.continuous.subtype_mk _) fun a b hab heq => ?_
  exact eq_of_specializes_of_isFinite' g hab (congrArg Subtype.val heq)

/-- **An invertible module on a normal integral scheme is the divisorial sheaf of a Cartier
divisor.** -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule Y L›
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- If `|M|` is composed of a free pencil, so is `|nM|` for `n > 0`. -/
private theorem isComposedOfFreePencil_nsmul (k : Type u) [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) {M : Divisor X}
    (h : IsComposedOfFreePencil k sX M) {n : ℕ} (hn : 0 < n) :
    IsComposedOfFreePencil k sX (n • M) := by
  have h' := h
  obtain ⟨hX, hM, ι, b, hloc, hdim⟩ := h
  have := hX.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have : CompactSpace X := by
    have := hX.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have := hM.isInvertibleModule_divisorialSheaf
  have := finiteDimensional_globalSections k sX M.divisorialSheaf
  obtain ⟨m, ⟨e⟩⟩ := exists_equiv_fin_of_linearSystemLocus_eq_top k _ b hloc
  have hg := generatesStalks_of_linearSystemLocus_eq_top k _ b e hloc
  rw [topologicalKrullDim_linearSystemImage_eq k _ b e hg hloc] at hdim
  -- the morphism `φ_{|M|} : X ⟶ ℙᵐ_k` and its Stein factorization
  set φ := toProjectiveSpaceOver (fun i => b (e i)) hg sX
  let sP := CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.terminal.from (Spec (.of k)))
    (CategoryTheory.Limits.terminal.from (projectiveSpaceAtUniverse.{u} m))
  have hφP : φ ≫ sP = sX := toProjectiveSpaceOver_fst _ _ _
  have : IsProper (φ ≫ sP) := by rw [hφP]; infer_instance
  have : IsProper φ := IsProper.of_comp φ sP
  obtain ⟨Y', q, g, ⟨hS⟩, -, hqs, hqiso, -, hgfin, hYvar, hYproj, hYnorm, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sP φ hφP
  have hcomp : q ≫ g = φ := hS.comp
  set sY := g ≫ sP
  have hY : MMP.Mori.IsProjectiveVariety k sY :=
    hYproj (isProjectiveMorphism_projectiveSpaceOver m (Spec (.of k)))
  have : IsNormal Y' := hYnorm inferInstance
  have := hY.toIsIntegral
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y' := by
    have := hY.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sY
  have hps : q ≫ sY = sX := by rw [← Category.assoc, hcomp, hφP]
  -- `Y'` has dimension at most one
  have hY1 : topologicalKrullDim Y' ≤ 1 := by
    refine (topologicalKrullDim_le_rdim_of_isFinite g).trans (le_of_eq ?_)
    rw [← rdim_comp_surjective (⇑g.base) hqs.surj, ← hdim]
    change rdim (⇑(q ≫ g).base) = _
    rw [hcomp]
    rfl
  -- the invertible sheaf `A = g^* 𝒪(1)` on `Y'`, with `q^* A ≅ 𝒪_X(M)`
  let t0 := projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))
  let A : Y'.Modules := (Scheme.Modules.pullback (g ≫ t0)).obj
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse m)
  have : Stacks.Ample.IsInvertibleModule Y' A :=
    Stacks.TwistPullbackPinned.isInvertibleModule_pullback_twistingSheafAtUniverse _
  have hpin : IsPinned ⟨M.divisorialSheaf, ‹_›, _, hg⟩
      (toProjectiveSpaceAtUniverse (fun i => b (e i)) hg) :=
    fun i => ι_toProjectiveSpaceAtUniverse _ hg i
  obtain ⟨β, -⟩ := isomorphic_tautological_of_isPinned hpin
  have hφt : q ≫ (g ≫ t0) = toProjectiveSpaceAtUniverse (fun i => b (e i)) hg := by
    rw [← Category.assoc, hcomp]
    exact toProjectiveSpaceOver_snd _ _ _
  let E1 : (Scheme.Modules.pullback q).obj A ≅ M.divisorialSheaf :=
    (Scheme.Modules.pullbackComp q (g ≫ t0)).app _ ≪≫ eqToIso (by rw [hφt]; rfl) ≪≫ β
  -- a Cartier divisor `B'` on `Y'` with `𝒪(B') ≅ A`, and its pull-back `B''` to `X`
  obtain ⟨B', hB'c, ⟨EA⟩⟩ := exists_isCartier_divisorialSheaf_iso A
  obtain ⟨B'', hpb⟩ := hB'c.exists_isPullback (f := q)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q B')
  let E2 : B''.divisorialSheaf ≅ (Scheme.Modules.pullback q).obj B'.divisorialSheaf :=
    hpb.divisorialSheafIso (hBc := hB'c)
  obtain ⟨χ, hχ⟩ : B''.LinearlyEquivalent M := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (E2 ≪≫ (Scheme.Modules.pullback q).mapIso EA ≪≫ E1)
  have hB'' : B'' = M + principalDivisor χ := by rw [← hχ]; abel
  -- transport to `Y'`, where the dimension is at most one
  have hB''c : IsComposedOfFreePencil k sX B'' := by
    rw [hB'']
    exact isComposedOfFreePencil_add_principalDivisor k sX h' χ
  have hY'B : IsComposedOfFreePencil k sY B' :=
    (isComposedOfFreePencil_iff_of_isPullback k sX sY hX hY q hps hqiso hB'c hpb).mp hB''c
  have hY'nB := isComposedOfFreePencil_nsmul_of_topologicalKrullDim_le_one k sY hY'B hY1 hn
  have hpbn := hpb.zsmul hB'c (n : ℤ)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q _)
  have hXnB : IsComposedOfFreePencil k sX ((n : ℤ) • B'') := by
    refine (isComposedOfFreePencil_iff_of_isPullback k sX sY hX hY q hps hqiso
      (hB'c.zsmul _) hpbn).mpr ?_
    rw [natCast_zsmul]
    exact hY'nB
  have hp : principalDivisor (χ ^ (n : ℤ)) = (n : ℤ) • principalDivisor χ := by
    ext E
    simp [PrimeDivisor.ord_pow]
  have hfin : (n : ℤ) • B'' + principalDivisor (χ ^ (n : ℤ))⁻¹ = n • M := by
    rw [MMP.Mori.principalDivisor_inv, hp, hB'', smul_add, natCast_zsmul]
    abel
  rw [← hfin]
  exact isComposedOfFreePencil_add_principalDivisor k sX hXnB _

/-- A morphism with `p_* 𝒪_X = 𝒪_Y` onto an integral scheme is dominant. -/
private theorem isDominant_of_isIso_app {X Y : Scheme.{u}} [IsIntegral Y] (p : X ⟶ Y)
    (hp : ∀ U : Y.Opens, IsIso (p.app U)) : IsDominant p := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨y, hy⟩ => ?_⟩
  by_contra hempty
  let V' : Y.Opens := ⟨V, hV⟩
  have hbot : p ⁻¹ᵁ V' = ⊥ := TopologicalSpace.Opens.ext <| Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => hempty ⟨p x, hx, x, rfl⟩
  have : Subsingleton Γ(X, p ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(Y, V') := (ConcreteCategory.bijective_of_isIso (p.app V')).1.subsingleton
  have h10 := congrArg (Y.presheaf.germ V' y hy).hom (Subsingleton.elim (1 : Γ(Y, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- **Free pencils under a crepant fibre space** (FA 15.7.1, 15.9). Let `p : X ⟶ Y` be a
morphism of normal projective varieties over `k` with `p_* 𝒪_X = 𝒪_Y`, and `L`, `N` `ℚ`-Cartier
`ℚ`-divisors on `X`, `Y` with `L ∼_ℚ p^* N`. Then `L` is eventually free and composed of a pencil
if and only if `N` is. -/
@[mmp "lem_fa15_free_pencil_crepant_morphism"]
public theorem isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : Mori.IsProjectiveVariety k sX) (hY : Mori.IsProjectiveVariety k sY)
    (p : X ⟶ Y) (hps : p ≫ sY = sX) (hp : ∀ U : Y.Opens, IsIso (p.app U))
    {L : QDivisor X} {N : QDivisor Y} (hL : L.IsQCartier) (hN : N.IsQCartier)
    (hLN : ∃ hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp,
      L.QLinearlyEquivalent (N.pullback hN hB)) :
    IsEventuallyFreePencil k sX L ↔ IsEventuallyFreePencil k sY N := by
  haveI := hX.toIsIntegral
  haveI := hY.toIsIntegral
  haveI : CompactSpace Y := by
    haveI := hY.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsDominant p := isDominant_of_isIso_app p hp
  obtain ⟨hB, m, hm, φ, hφ⟩ := hLN
  constructor
  · rintro ⟨k', hk', M, hM, hMf⟩
    obtain ⟨n, hn, D, hD, hDc⟩ := hN.exists_pos
    obtain ⟨D', hD', hDp⟩ := QDivisor.isPullback_pullback hN hB n hn D hD hDc
    refine ⟨k' * m * n, by positivity, ((k' * m : ℕ) : ℤ) • D, ?_, ?_⟩
    · rw [map_zsmul, hD, smul_smul]; push_cast; ring_nf
    · refine (isComposedOfFreePencil_iff_of_isPullback k sX sY hX hY p hps hp (hDc.zsmul _)
        (hDp.zsmul hDc _ (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant
          p _))).mp ?_
      have key : ((k' * m : ℕ) : ℤ) • D' =
          ((m * n : ℕ) • M) + principalDivisor (φ ^ (-((k' * n : ℕ) : ℤ))) := by
        apply Divisor.toQDivisor_injective
        ext E
        have h1 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hφ
        have h2 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hM
        have h3 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hD'
        simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
          DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
          PrimeDivisor.ord_zpow, map_zsmul, map_add, map_nsmul, zsmul_eq_mul, nsmul_eq_mul,
          smul_eq_mul] at h1 h2 h3 ⊢
        push_cast at h1 h2 h3 ⊢
        linear_combination ((k' : ℚ) * m) * h3 - ((m : ℚ) * n) * h2 - ((k' : ℚ) * n) * h1
      rw [key]
      exact isComposedOfFreePencil_add_principalDivisor k sX
        (isComposedOfFreePencil_nsmul k sX hMf (by positivity)) _
  · rintro ⟨k', hk', M, hM, hMf⟩
    have hMc : M.IsCartier := hMf.2.1
    obtain ⟨D', hD', hDp⟩ := QDivisor.isPullback_pullback hN hB k' hk' M hM hMc
    refine ⟨k' * m, by positivity, ((m : ℤ) • D') + principalDivisor (φ ^ (k' : ℤ)), ?_, ?_⟩
    · ext E
      have h1 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hφ
      have h3 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hD'
      simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
        PrimeDivisor.ord_zpow, map_zsmul, map_add, map_nsmul, zsmul_eq_mul, nsmul_eq_mul,
        smul_eq_mul] at h1 h3 ⊢
      push_cast at h1 h3 ⊢
      linear_combination (m : ℚ) * h3 - (k' : ℚ) * h1
    · refine isComposedOfFreePencil_add_principalDivisor k sX ?_ _
      simpa [natCast_zsmul] using isComposedOfFreePencil_nsmul k sX
        ((isComposedOfFreePencil_iff_of_isPullback k sX sY hX hY p hps hp hMc hDp).mpr hMf) hm

end FreePencil

section BlowUp

open TopologicalSpace MMP.Threefold.Resolution

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {a : Fin n → ℚ}

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds _))

/-- **The log discrepancy vector after blowing up a point.** Let `g : Y ⟶ X` be a resolution of
`(X, P)` with exceptional curves `E_1, …, E_n` and log discrepancy vector `a` of `(X, P; B)`,
`y ∈ g⁻¹(P)` a closed point, `π : Y' ⟶ Y` the blow-up of `y` and `F = π⁻¹(y)_red`. Then `g ∘ π`
is a resolution of `(X, P)` whose exceptional curves are the birational transforms
`E'_j = π⁻¹_* E_j` and `F`, and a vector `a'` is the log discrepancy vector of `(X, P; B)` on
`g ∘ π` if and only if `a'_{E'_j} = a_j` for every `j` and `a'_F = 2 - mult_y Θ_{g,a}`, where
`Θ_{g,a} = MMP.Flips.logPullbackBoundary g B E a`. -/
@[mmp "lem_fa3_blowup_point_log_discrepancy"]
public theorem isGermLogDiscrepancyVector_snoc_blowUp_iff
    (ha : IsGermLogDiscrepancyVector sX P B g E a) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hyP : g y = P) {F : Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :
    haveI := (ha.2.1.comp_blowUpToBase hy hyP).quasiCompact_comp
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (ha.2.1.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (ha.2.1.comp_blowUpToBase hy hyP).isSmoothResolution.isSmoothScheme).2
    IsGermResolution sX P (πy ≫ g) ∧
      ∃ E' : Fin n → Mori.PrimeDivisor Y'y,
        (∀ j, inverseTransformPrimeDivisor πy (E j) = some (E' j)) ∧
        IsExceptionalCurveEnumeration (πy ≫ g) P (Fin.snoc E' F : Fin (n + 1) → _) ∧
        ∀ a' : Fin (n + 1) → ℚ,
          IsGermLogDiscrepancyVector sX P B (πy ≫ g) (Fin.snoc E' F : Fin (n + 1) → _) a' ↔
            a' = (Fin.snoc a (2 - (logPullbackBoundary g B E a).multiplicityAt y) :
              Fin (n + 1) → ℚ) :=
  isGermLogDiscrepancyVector_snoc_blowUp_iff_of_isCanonicalDivisor ha hy hyP hF
    fun K hK => isCanonicalDivisor_pullback_add_single_blowUp_singleton ha.2.1.isVariety
      ha.2.1.isSmoothResolution.isSmoothScheme ha.2.1.topologicalKrullDim_eq hy hF hK

end BlowUp

end MMP.Flips

end
