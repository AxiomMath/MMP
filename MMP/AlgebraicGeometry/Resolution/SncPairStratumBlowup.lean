module
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Jacobian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity

/-!
# Foundational lemmas: snc blow-ups, base change, isolated fibre points, relative ampleness

This file collects independent foundational results used by the minimal model program.

* **Blowing up an snc stratum.** Let `Y` be smooth over a perfect field `k` with a simple normal
  crossing divisor `∑_j H_j`, and `W` an irreducible component of `H_k ∩ H_l`, `k ≠ l`, with its
  reduced structure. The blow-up `π : B_W Y → Y` is smooth, the exceptional divisor `E = π⁻¹ W`
  together with the strict transforms `H'_j = π⁻¹(H_j ∖ W)‾` is snc, and every component of the
  intersection of two new boundary components is either the strict transform of a component
  `V ≠ W` of `H_i ∩ H_j`, or lies on `E ∩ H'_j` with `H_j ∩ W ≠ ∅`. In snc coordinates near `W`
  the ideal of `W` is `(x_1, x_2)`, and the blow-up charts are coordinate charts in which `E` and
  the `H'_j` are coordinate hyperplanes.
* **Field extensions.** For a quasi-compact quasi-separated morphism `f : X ⟶ Z` of `k`-schemes
  and a field extension `k ⊆ K`, `f_* 𝒪_X = 𝒪_Z` if and only if `(f_K)_* 𝒪_{X_K} = 𝒪_{Z_K}`.
  Flat base change of sections makes `Γ(X_K, f_K⁻¹ W)` the pushout of
  `Γ(X, f⁻¹ U) ← Γ(Z, U) → Γ(Z_K, W)`; bijectivity is preserved by pushouts and descends along
  the faithfully flat maps `Γ(Z, U) → Γ(Z_K, π⁻¹ U)`.
* **Isolated fibre points.** For a morphism of schemes of finite type over a Noetherian scheme,
  the points isolated in their fibre form an open set (Zariski's main theorem, through the
  quasi-finite locus). A morphism `g : S ⟶ X` of smooth `k`-varieties of the same dimension `n`
  whose pull-back of top forms `g^*Ω^n_X ⟶ Ω^n_S` is surjective on stalks at `s` is unramified
  at `s`, so `s` is isolated in its fibre: a unit determinant of `d(g^♯w_i)` against a basis of
  `Ω_{𝒪_{S,s}/k}` forces `Ω_{𝒪_{S,s}/𝒪_{X,g(s)}} = 0`.
* **Density.** For irrational `θ` and an integer `N`, the fractional parts of `x θ`, `x ≥ N`,
  are dense in `[0, 1]`: Dirichlet's approximation theorem gives a small nonzero step
  `δ = q θ - p`, and the points `N θ + j δ` walk around `ℝ / ℤ` with gaps `|δ|`.
* **Relative ampleness.** Over an affine base, a coherent sheaf twisted by a high power of a
  relatively ample invertible sheaf is globally generated; a proper morphism to a Noetherian
  scheme with a relatively ample invertible sheaf, or a proper morphism of varieties with a
  relatively ample Cartier divisor, is projective.

## Main results

* `MMP.Resolution.blowUp_snc_pair_stratum`: blowing up a component of a double intersection of
  an snc divisor.
* `MMP.Foundations.isIso_app_iff_isIso_baseChange_app`: `f_* 𝒪_X = 𝒪_Z` descends along and
  ascends to a field extension.
* `MMP.Foundations.isPushout_app_pullbackMap_and_isIso_app_iff`: for a proper `f` of finite type
  `k`-schemes, the base change square of sections is a pushout over every pair of affine opens
  (so `(f_* 𝒪_X) ⊗_k K ≅ (f_K)_* 𝒪_{X_K}`), and `f_* 𝒪_X = 𝒪_Z ↔ (f_K)_* 𝒪_{X_K} = 𝒪_{Z_K}`.
* `MMP.isOpen_setOf_isolated_mem_fiber`: the locus of points isolated in their fibre is open.
* `MMP.Intersection.isOpen_singleton_asFiber_of_surjective_stalk_jacobianSection`: an invertible
  top differential gives an isolated fibre point.
* `MMP.Foundation.Irrational.Icc_subset_closure_fract_mul`: density of fractional parts of a
  tail of an irrational progression.
* `MMP.Mori.isGeneratedByGlobalSections_tensor_tensorPowModule_of_isRelativelyAmple`: relative
  Serre generation over an affine base.
* `MMP.isProjective_of_isProper_of_isRelativelyAmple`,
  `MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple`: proper morphisms with a relatively
  ample invertible sheaf, resp. Cartier divisor, are projective.

## Implementation notes

* The new boundary of the blow-up is indexed by `Option Λ`: `none` is the exceptional divisor
  `Z.comap π` and `some j` the reduced closure of `π⁻¹(H_j ∖ W)`. The source works over `ℂ`; the
  statement holds over any perfect field, but not over an imperfect one, where a component of
  `H_k ∩ H_l` can be a point with inseparable residue field whose blow-up is not smooth.
* `f_* 𝒪_X = 𝒪_Z` is spelled `∀ U, IsIso (f.app U)`, and base changes are `pullback` along
  `Spec K ⟶ Spec k`; only quasi-compactness and quasi-separatedness of `f` are needed.
* Being isolated in the fibre is phrased either in the topology of `X` (an open `U ∋ x` with
  `U ∩ φ⁻¹{φ x} = {x}`) or as openness of `{g.asFiber s}` in the scheme-theoretic fibre; the two
  agree through `Scheme.Hom.fiberHomeo`.
* "Dense in `[0, 1]`" is `Set.Icc 0 1 ⊆ closure S`.
* Relative ampleness is the local form `MMP.Mori.IsRelativelyAmple`; it upgrades to ampleness over
  every affine open of the base ([Stacks, Tag 01VJ]). Projectivity is
  `AlgebraicGeometry.IsProjective` ([Stacks, Tag 01W8]) and is obtained from quasi-projectivity
  and properness ([Stacks, Tag 0BCL]) rather than by embedding into `𝐏(f_* L^m)` directly.
  Cartier divisors are `MMP.Mori.Divisor.IsCartier` on a normal scheme, hence `[IsNormal X]`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.24]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98], 1.41
* [EGA II, 5.5.3, 4.6], [EGA IV, 13.1.4]
* [The Stacks Project, Tags 01Q3, 01VJ, 01W8, 02G1, 02GF, 02V5, 0BCL][stacks-project]
-/

universe u

/-! ### Blowing up a component of a double intersection of an snc divisor -/

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

/-- If the inverse image in `Spec 𝒪_{Y,y}` of a closed set `T` is `V(P)` for a prime `P`, then
the ideal of every irreducible component of `T` through `y` has stalk `P` at `y`. -/
private theorem stalk_componentsFamily_eq_of_preimage_eq_zeroLocus {Y : Scheme.{u}} {T : Set Y}
    (hT : IsClosed T) {y : Y} (P : Ideal (Y.presheaf.stalk y)) [hP : P.IsPrime]
    (hTy : Y.fromSpecStalk y ⁻¹' T = PrimeSpectrum.zeroLocus (P : Set (Y.presheaf.stalk y)))
    (V : componentsOf T) (hyV : y ∈ (V : Set Y)) :
    IdealSheafData.stalk (componentsFamily T V) y = P := by
  obtain ⟨ξ, hξT, hVξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hT V.2
  have hξy : ξ ⤳ y := specializes_iff_mem_closure.mpr (hVξ ▸ hyV)
  obtain ⟨q, hq⟩ : ξ ∈ Set.range (Y.fromSpecStalk y) := by
    rwa [Scheme.range_fromSpecStalk]
  have hstalk : IdealSheafData.stalk (componentsFamily T V) y = q.asIdeal := by
    have : componentsFamily T V = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({Y.fromSpecStalk y q} : Set Y)) := by
      unfold componentsFamily
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, hq, ← hVξ,
        (Aux.isClosed_of_mem_componentsOf hT V.2).closure_eq]
    rw [this]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q
  have hqT : q ∈ Y.fromSpecStalk y ⁻¹' T := by
    rwa [Set.mem_preimage, hq]
  rw [hTy] at hqT
  let p' : PrimeSpectrum (Y.presheaf.stalk y) := ⟨P, hP⟩
  have hp'q : p' ≤ q := (PrimeSpectrum.mem_zeroLocus _ _).1 hqT
  have hp'T : Y.fromSpecStalk y p' ∈ T := by
    have : p' ∈ Y.fromSpecStalk y ⁻¹' T := by
      rw [hTy]; exact (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl
    exact this
  have hsp : Y.fromSpecStalk y p' ⤳ ξ :=
    hq ▸ ((PrimeSpectrum.le_iff_specializes _ _).1 hp'q).map (Y.fromSpecStalk y).continuous
  have hsub : (V : Set Y) ⊆ closure {Y.fromSpecStalk y p'} := by
    rw [hVξ]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have hcl : closure {Y.fromSpecStalk y p'} = (V : Set Y) :=
    (V.2.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hp'T) hT⟩ hsub).antisymm hsub
  have hpq : p' = q := by
    apply (Y.fromSpecStalk y).isEmbedding.injective
    rw [hq]
    refine Inseparable.eq ?_
    rw [inseparable_iff_closure_eq, hcl, hVξ]
  rw [hstalk, ← hpq]

/-- At a point `x` of a component `W` of `H_{i₁} ∩ H_{i₂}`, in snc coordinates `z` at `x`, the
ideal of `W` has stalk `(z_a, z_b)` with `a ≠ b` the coordinates of `H_{i₁}` and `H_{i₂}`. -/
private theorem exists_stalk_componentsFamily_inter_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] {Λ : Type*}
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) (x : Y)
    (hx : x ∈ (W : Set Y)) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk x) (c : {i // x ∈ (H i).support} → Fin n)
      (s : Finset (Fin n)), s.card ≤ 2 ∧
      MMP.Mori.IsRegularSystemOfParameters z ∧
      (∀ i, IdealSheafData.stalk (H i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c ∧
      IdealSheafData.stalk (componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W) x =
        Ideal.span (z '' (s : Set (Fin n))) := by
  classical
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hH.2 x
  have hxT : x ∈ ((H i₁).support ∩ (H i₂).support : Set Y) := W.2.1.2 hx
  set a := c ⟨i₁, hxT.1⟩
  set b := c ⟨i₂, hxT.2⟩
  refine ⟨n, z, c, {a, b}, Finset.card_le_two, hz, hc, hinj, ?_⟩
  have hP := span_image_isPrime_of_isRegularSystemOfParameters hz {a, b}
  refine stalk_componentsFamily_eq_of_preimage_eq_zeroLocus
    (((H i₁).support.isClosed).inter (H i₂).support.isClosed) _ ?_ W hx
  ext p
  have h1 := fromSpecStalk_mem_support_iff_stalk_le (H i₁) x p
  have h2 := fromSpecStalk_mem_support_iff_stalk_le (H i₂) x p
  rw [hc ⟨i₁, hxT.1⟩, Ideal.span_le] at h1
  rw [hc ⟨i₂, hxT.2⟩, Ideal.span_le] at h2
  refine (and_congr h1 h2).trans ?_
  refine Iff.trans ?_ (PrimeSpectrum.mem_zeroLocus _ _).symm
  rw [SetLike.coe_subset_coe, Ideal.span_le]
  simp [Set.image_insert_eq, Set.insert_subset_iff, a, b]

/-- In an snc family, no component of `D_a ∩ D_b`, `a ≠ b`, lies in a third member `D_c`. -/
private theorem not_subset_support_of_mem_componentsOf_inter {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] {Λ : Type*}
    {D : Λ → X.IdealSheafData} (hD : IsSNCFamily s D) {a b c : Λ} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) {C : Set X}
    (hC : C ∈ componentsOf ((D a).support ∩ (D b).support : Set X)) :
    ¬ C ⊆ (D c).support := by
  classical
  intro hsub
  have hT : IsClosed ((D a).support ∩ (D b).support : Set X) :=
    ((D a).support.isClosed).inter (D b).support.isClosed
  obtain ⟨η, -, hCη⟩ := Aux.exists_eq_closure_of_mem_componentsOf hT hC
  have hηC : η ∈ C := hCη ▸ subset_closure rfl
  obtain ⟨n, w, cc, t, ht, hw, -, hinj, hst⟩ :=
    exists_stalk_componentsFamily_inter_eq s D hD hab ⟨C, hC⟩ η hηC
  have hmax : IdealSheafData.stalk (componentsFamily ((D a).support ∩ (D b).support : Set X)
      ⟨C, hC⟩) η = IsLocalRing.maximalIdeal _ := by
    have : componentsFamily ((D a).support ∩ (D b).support : Set X) ⟨C, hC⟩ =
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          ({X.fromSpecStalk η (IsLocalRing.closedPoint _)} : Set X)) := by
      unfold componentsFamily
      congr 1
      ext1
      rw [Closeds.coe_closure, Closeds.coe_closure, Scheme.fromSpecStalk_closedPoint, ← hCη]
      change closure C = C
      rw [hCη, closure_closure]
    rw [this]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk η _
  rw [hst] at hmax
  have hηa : η ∈ (D a).support := (hC.1.2 hηC).1
  have hηb : η ∈ (D b).support := (hC.1.2 hηC).2
  have hηc : η ∈ (D c).support := hsub hηC
  have h3 : 3 ≤ n := by
    have hd : ∀ {i j : Λ} (hi : η ∈ (D i).support) (hj : η ∈ (D j).support), i ≠ j →
        cc ⟨i, hi⟩ ≠ cc ⟨j, hj⟩ := fun _ _ h => h ∘ congrArg Subtype.val ∘ @hinj _ _
    have h := Finset.card_le_univ ({cc ⟨a, hηa⟩, cc ⟨b, hηb⟩, cc ⟨c, hηc⟩} : Finset (Fin n))
    rwa [Finset.card_eq_three.2 ⟨_, _, _, hd _ _ hab, hd _ _ hca.symm, hd _ _ hcb.symm, rfl⟩,
      Fintype.card_fin] at h
  have hht : (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).height ≤ (t.image w).card := by
    refine Ideal.height_le_card_of_mem_minimalPrimes_span_finset ?_
    rw [Finset.coe_image, hmax, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hle : (t.image w).card ≤ 2 := Finset.card_image_le.trans ht
  have hdim := hw.2
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hdim
  have h' := WithBot.coe_inj.1 hdim
  rw [h'] at hht
  have : n ≤ 2 := (Nat.cast_le (α := ℕ∞)).1 hht |>.trans hle
  omega

/-- The blow-up of a component of a double intersection is smooth. -/
private theorem smooth_blowUp_componentsFamily_inter {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [Smooth sY] {Λ : Type*}
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) :
    Smooth (blowUpToBase (componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W) ≫ sY) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  set Z := componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W
  have hreg :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sY).1 inferInstance
  have hZsm : Smooth (Z.subschemeι ≫ sY) := by
    rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    intro y
    have hx : Z.subschemeι y ∈ (W : Set Y) := by
      have hy : Z.subschemeι y ∈ (Z.support : Set Y) := by
        rw [← Z.range_subschemeι]; exact ⟨y, rfl⟩
      rwa [SetLike.mem_coe, ← SetLike.mem_coe, coe_support_componentsFamily
        (((H i₁).support.isClosed).inter (H i₂).support.isClosed)] at hy
    obtain ⟨n, z, -, s, -, hz, -, -, hstalk⟩ :=
      exists_stalk_componentsFamily_inter_eq sY H hH hne W _ hx
    have := hreg (Z.subschemeι y)
    obtain ⟨hq, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
    rw [← hstalk, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk Z y] at hq
    let f := (Z.subschemeι.stalkMap y).hom
    let e := f.quotientKerEquivOfSurjective (Z.subschemeι.stalkMap_surjective y)
    exact IsRegularLocalRing.of_ringEquiv (R := _ ⧸ RingHom.ker f) e
  exact (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY Z
    ⟨(MMP.Mori.isSmoothScheme_iff sY).2 inferInstance,
      (MMP.Mori.isSmoothScheme_iff _).2 hZsm⟩).1

/-- In a quasi-sober space in which every point has a Noetherian open neighbourhood, every point
of the closure of a locally closed set `S = C ∩ O` is a specialization of a point of `S`. -/
private theorem exists_mem_specializes_of_mem_closure_of_forall_exists_noetherianSpace {α : Type*}
    [TopologicalSpace α] [QuasiSober α]
    (hloc : ∀ y : α, ∃ U : Set α, IsOpen U ∧ y ∈ U ∧ NoetherianSpace U)
    {C O : Set α} (hC : IsClosed C) (hO : IsOpen O) {y : α}
    (hy : y ∈ closure (C ∩ O)) : ∃ s ∈ C ∩ O, s ⤳ y := by
  obtain ⟨U, hU, hyU, hN⟩ := hloc y
  have := hU.isOpenEmbedding_subtypeVal.quasiSober
  have hy' : (⟨y, hyU⟩ : U) ∈ closure (((↑) : U → α) ⁻¹' C ∩ ((↑) : U → α) ⁻¹' O) := by
    rw [← Set.preimage_inter,
      ← hU.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
    exact hy
  obtain ⟨s, hs, hsy⟩ := exists_mem_specializes_of_mem_closure
    (hC.preimage continuous_subtype_val) (hO.preimage continuous_subtype_val) hy'
  exact ⟨s, hs, hsy.map continuous_subtype_val⟩

/-- In a locally Noetherian scheme, every point of the closure of a locally closed set
`S = C ∩ O` is a specialization of a point of `S`. -/
private theorem exists_mem_specializes_of_mem_closure_scheme {X : Scheme.{u}}
    [IsLocallyNoetherian X] {C O : Set X} (hC : IsClosed C) (hO : IsOpen O) {y : X}
    (hy : y ∈ closure (C ∩ O)) : ∃ s ∈ C ∩ O, s ⤳ y := by
  refine exists_mem_specializes_of_mem_closure_of_forall_exists_noetherianSpace (fun y => ?_)
    hC hO hy
  obtain ⟨U, hU, hyU, -⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y ∈ (⊤ : X.Opens) from trivial)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨U, U.isOpen, hyU, noetherianSpace_of_isAffineOpen U hU⟩

/-- Local coordinates on the blow-up of a centre having snc with an snc family, for a locally
Noetherian base. -/
private theorem exists_coordinates_blowUpTransformFamily_of_isLocallyNoetherian {k : Type u}
    [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {Z : Y.IdealSheafData}
    (hZ : HasSNCWith D Z) (x' : blowUp Z) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  classical
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  set π := blowUpToBase Z
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x' with hf'
  have key : ∀ S : Set Y, f' ⁻¹' (π ⁻¹' S) =
      PrimeSpectrum.comap φ ⁻¹' (Y.fromSpecStalk (π x') ⁻¹' S) := by
    intro S
    have h := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x')
    refine Set.ext fun p => ?_
    change π (f' p) ∈ S ↔ Y.fromSpecStalk (π x') (PrimeSpectrum.comap φ p) ∈ S
    rw [← Scheme.Hom.comp_apply, hf', ← h]
    rfl
  have hmem : ∀ (I : Y.IdealSheafData) {g : Y.presheaf.stalk (π x')},
      IdealSheafData.stalk I (π x') = Ideal.span {g} →
      ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' p) ∈ I.support ↔ φ g ∈ p.asIdeal := by
    intro I g hg p
    have := Set.ext_iff.1 (key I.support) p
    change π (f' p) ∈ (I.support : Set Y) ↔ _
    refine this.trans ?_
    change Y.fromSpecStalk (π x') (PrimeSpectrum.comap φ p) ∈ (I.support : Set Y) ↔ _
    rw [fromSpecStalk_mem_support_iff_stalk_le, hg, Ideal.span_singleton_le_iff_mem]
    rfl
  have hgen : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), f' p ⤳ x' :=
    fun p => Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
  set T : Λ → Set (blowUp Z) :=
    fun l => closure (π ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y)))
  have hsuppT : ∀ l, ((blowUpTransformFamily D Z (Sum.inl l)).support : Set (blowUp Z)) = T l :=
    coe_support_blowUpTransformFamily_inl D Z
  have hTsub : ∀ l, T l ⊆ π ⁻¹' ((D l).support : Set Y) := fun l =>
    closure_minimal (fun _ h => h.1) ((D l).support.isClosed.preimage π.continuous)
  have hTsub' : ∀ l, x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support →
      π x' ∈ (D l).support := fun l h => hTsub l (by rwa [← hsuppT])
  have hstalkT : ∀ l {N : ℕ} {w : Fin N → (blowUp Z).presheaf.stalk x'},
      IsRegularSystemOfParameters w → ∀ t : Fin N,
      (∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), f' p ∈ T l ↔ w t ∈ p.asIdeal) →
      IdealSheafData.stalk (blowUpTransformFamily D Z (Sum.inl l)) x' = Ideal.span {w t} := by
    intro l N w hw t h
    change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal _) x' = _
    rw [stalk_vanishingIdeal_eq, ← hw.vanishingIdeal_zeroLocus_singleton t]
    congr 1
    ext p
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    exact h p
  have hclosed : (blowUp Z).fromSpecStalk x' (IsLocalRing.closedPoint _) = x' :=
    Scheme.fromSpecStalk_closedPoint
  by_cases hx : π x' ∈ Z.support
  · -- over the centre: the coordinates of a chart
    obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := hZ (π x') hx
    obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
      exists_chart_coordinates Z x' hx hz hJ
    have hE : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        π (f' p) ∈ Z.support ↔ w i₀ ∈ p.asIdeal := by
      intro p
      refine (Set.ext_iff.1 (key Z.support) p).trans
        ((Set.ext_iff.1 (preimage_fromSpecStalk_support Z (π x'))
          (PrimeSpectrum.comap φ p)).trans ?_)
      rw [hJ]
      refine (PrimeSpectrum.mem_zeroLocus _ _).trans ?_
      rw [SetLike.coe_subset_coe, Ideal.span_le]
      constructor
      · intro h
        rw [hwi₀]
        exact h ⟨m, hmJ, rfl⟩
      · rintro h _ ⟨j, hj, rfl⟩
        change φ (z j) ∈ p.asIdeal
        by_cases hjm : j = m
        · rwa [hjm, ← hwi₀]
        by_cases hjU : j ∈ U
        · obtain ⟨u, -, hu⟩ := hunit j hjU
          rw [hu]
          exact Ideal.mul_mem_left _ _ h
        · rw [hin j hj hjm hjU]
          exact Ideal.mul_mem_left _ _ h
    have hrel1 : ∀ j, j ≠ m → j ∉ U → ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        w (σ j) ∈ p.asIdeal → φ (z j) ∈ p.asIdeal := by
      intro j hjm hjU p h
      by_cases hjJ : j ∈ J
      · rw [hin j hjJ hjm hjU]
        exact Ideal.mul_mem_right _ _ h
      · rwa [← hout j hjJ]
    have hrel2 : ∀ j, j ≠ m → j ∉ U → ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        w i₀ ∉ p.asIdeal → φ (z j) ∈ p.asIdeal → w (σ j) ∈ p.asIdeal := by
      intro j hjm hjU p h0 h
      by_cases hjJ : j ∈ J
      · rw [hin j hjJ hjm hjU] at h
        exact (p.isPrime.mem_or_mem h).resolve_right h0
      · rwa [hout j hjJ]
    have hbad : ∀ j, (j = m ∨ j ∈ U) → ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
        φ (z j) ∈ p.asIdeal → w i₀ ∈ p.asIdeal := by
      rintro j (rfl | hjU) p h
      · rwa [hwi₀]
      · obtain ⟨u, hu, hu'⟩ := hunit j hjU
        rw [hu'] at h
        refine (p.isPrime.mem_or_mem h).resolve_left fun h' => ?_
        exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
    -- the generic point of a coordinate hyperplane `w_{σ j} = 0` lies over `D_l ∖ Z`
    have hP₀ : ∀ (l : Λ) (hl : π x' ∈ (D l).support), c ⟨l, hl⟩ ≠ m → c ⟨l, hl⟩ ∉ U →
        f' ⟨Ideal.span {w (σ (c ⟨l, hl⟩))},
          span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩ ∈
          π ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y)) := by
      intro l hl hjm hjU
      refine ⟨(hmem (D l) (hc ⟨l, hl⟩) _).2 (hrel1 _ hjm hjU _ (Ideal.subset_span rfl)),
        fun hZ' => ?_⟩
      exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw (hσ₀ _ hjm hjU)
        ((hE _).1 hZ')
    have hKS : ∀ (l : Λ) (hl : π x' ∈ (D l).support) (p : PrimeSpectrum _),
        f' p ∈ T l ↔ (c ⟨l, hl⟩ ≠ m ∧ c ⟨l, hl⟩ ∉ U) ∧ w (σ (c ⟨l, hl⟩)) ∈ p.asIdeal := by
      intro l hl p
      constructor
      · intro hp
        have hp' : f' p ∈ closure (π ⁻¹' ((D l).support : Set Y) ∩
            (π ⁻¹' (Z.support : Set Y))ᶜ) := by
          rwa [← Set.preimage_compl, ← Set.preimage_inter, ← Set.sdiff_eq]
        obtain ⟨s, hs, hsp⟩ := exists_mem_specializes_of_mem_closure_scheme
          ((D l).support.isClosed.preimage π.continuous)
          ((Z.support.isClosed.preimage π.continuous).isOpen_compl) hp'
        obtain ⟨q, rfl⟩ : s ∈ Set.range f' := by
          rw [Scheme.range_fromSpecStalk]; exact hsp.trans (hgen p)
        have hqp : q.asIdeal ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes q p).2
          ((f'.isEmbedding.isInducing.specializes_iff).1 hsp)
        have h1 : φ (z (c ⟨l, hl⟩)) ∈ q.asIdeal := (hmem (D l) (hc ⟨l, hl⟩) q).1 hs.1
        have h0 : w i₀ ∉ q.asIdeal := fun h => hs.2 ((hE q).2 h)
        have hgood : c ⟨l, hl⟩ ≠ m ∧ c ⟨l, hl⟩ ∉ U := by
          by_contra hcon
          rw [not_and_or, not_not, not_not] at hcon
          exact h0 (hbad _ hcon q h1)
        exact ⟨hgood, hqp (hrel2 _ hgood.1 hgood.2 q h0 h1)⟩
      · rintro ⟨⟨hjm, hjU⟩, hp⟩
        have hle : (⟨Ideal.span {w (σ (c ⟨l, hl⟩))},
            span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩ :
            PrimeSpectrum _) ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hp
        exact (((PrimeSpectrum.le_iff_specializes _ _).1 hle).map f'.continuous).mem_closed
          isClosed_closure (subset_closure (hP₀ l hl hjm hjU))
    have hgoodT : ∀ l (h : x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support),
        c ⟨l, hTsub' l h⟩ ≠ m ∧ c ⟨l, hTsub' l h⟩ ∉ U := by
      intro l h
      have h' : f' (IsLocalRing.closedPoint _) ∈ T l := by
        rwa [hclosed, ← hsuppT]
      exact ((hKS l (hTsub' l h) _).1 h').1
    let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N := fun i =>
      match i with
      | ⟨Sum.inl l, h⟩ => σ (c ⟨l, hTsub' l h⟩)
      | ⟨Sum.inr _, _⟩ => i₀
    refine ⟨N, w, c', hw, ?_, ?_⟩
    · rintro ⟨(l | u), h⟩
      · refine hstalkT l hw _ fun p => ?_
        rw [hKS l (hTsub' l h) p]
        exact and_iff_right (hgoodT l h)
      · change IdealSheafData.stalk (Z.comap π) x' = Ideal.span {w i₀}
        rw [IdealSheafData.stalk_comap, hJ, Ideal.map_span]
        refine le_antisymm (Ideal.span_le.2 ?_) ?_
        · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
          change φ (z j) ∈ Ideal.span {w i₀}
          by_cases hjm : j = m
          · rw [hjm, ← hwi₀]; exact Ideal.subset_span rfl
          by_cases hjU : j ∈ U
          · obtain ⟨v, -, hv⟩ := hunit j hjU
            rw [hv]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
          · rw [hin j hj hjm hjU]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
        · rw [Ideal.span_singleton_le_iff_mem, hwi₀]
          exact Ideal.subset_span ⟨z m, ⟨m, hmJ, rfl⟩, rfl⟩
    · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
      · change σ (c ⟨a, hTsub' a ha⟩) = σ (c ⟨b, hTsub' b hb⟩) at hab
        by_contra hne
        have hab' : a ≠ b := fun h => hne (by subst h; rfl)
        have hcab : c ⟨a, hTsub' a ha⟩ ≠ c ⟨b, hTsub' b hb⟩ := fun h =>
          hab' (congrArg Subtype.val (hinj h))
        obtain ⟨hga, hga'⟩ := hgoodT a ha
        obtain ⟨hgb, hgb'⟩ := hgoodT b hb
        set P₀ : PrimeSpectrum ((blowUp Z).presheaf.stalk x') :=
          ⟨Ideal.span {w (σ (c ⟨a, hTsub' a ha⟩))},
            span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩
        have hPa := hP₀ a (hTsub' a ha) hga hga'
        have hPb := hP₀ b (hTsub' b hb) hgb hgb'
        rw [← hab] at hPb
        set g := f' P₀
        obtain ⟨n', z', c'', hz', -, hinj'⟩ := hD.2 (π g)
        have hne' : c'' ⟨a, hPa.1⟩ ≠ c'' ⟨b, hPb.1⟩ := fun h =>
          hab' (congrArg Subtype.val (hinj' h))
        have h2 : 2 ≤ n' := by
          have := (c'' ⟨a, hPa.1⟩).2
          have := (c'' ⟨b, hPb.1⟩).2
          have : (c'' ⟨a, hPa.1⟩ : ℕ) ≠ c'' ⟨b, hPb.1⟩ := fun h => hne' (Fin.ext h)
          omega
        have hiso : IsIso (π.stalkMap g) :=
          isIso_stalkMap_of_isIso_morphismRestrict π
            (isIso_blowUpToBase_restrict_compl_support Z)
            (show g ∈ π ⁻¹ᵁ Z.support.compl from hPa.2)
        have hdim : ringKrullDim (Y.presheaf.stalk (π g)) =
            ringKrullDim ((blowUp Z).presheaf.stalk g) :=
          ringKrullDim_eq_of_ringEquiv (asIso (π.stalkMap g)).commRingCatIsoToRingEquiv
        have hdim2 : ringKrullDim ((blowUp Z).presheaf.stalk g) =
            (P₀.asIdeal.height : WithBot ℕ∞) := ringKrullDim_stalk_fromSpecStalk (blowUp Z) x' P₀
        rw [hz'.2, hdim2] at hdim
        have hle := hw.height_span_singleton_le_one (σ (c ⟨a, hTsub' a ha⟩))
        have : (n' : ℕ∞) ≤ 1 := by
          have h' : ((n' : ℕ∞) : WithBot ℕ∞) = (P₀.asIdeal.height : WithBot ℕ∞) := hdim
          rw [WithBot.coe_inj] at h'
          rwa [h']
        have : n' ≤ 1 := by exact_mod_cast this
        omega
      · change σ (c ⟨a, hTsub' a ha⟩) = i₀ at hab
        exact absurd hab (hσ₀ _ (hgoodT a ha).1 (hgoodT a ha).2)
      · change i₀ = σ (c ⟨b, hTsub' b hb⟩) at hab
        exact absurd hab.symm (hσ₀ _ (hgoodT b hb).1 (hgoodT b hb).2)
      · rfl
  · -- away from the centre the blow-up is a local isomorphism
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hD.2 (π x')
    have hiso : IsIso (π.stalkMap x') :=
      isIso_stalkMap_of_isIso_morphismRestrict π (isIso_blowUpToBase_restrict_compl_support Z)
        (show x' ∈ π ⁻¹ᵁ Z.support.compl from hx)
    let e := (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv
    have hw : IsRegularSystemOfParameters fun i => φ (z i) :=
      isRegularSystemOfParameters_map_ringEquiv e hz
    have hnotE : ∀ u, x' ∉ (blowUpTransformFamily D Z (Sum.inr u)).support := by
      intro u h
      rw [← SetLike.mem_coe, coe_support_blowUpTransformFamily_inr] at h
      exact hx h
    let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin n := fun i =>
      match i with
      | ⟨Sum.inl l, h⟩ => c ⟨l, hTsub' l h⟩
      | ⟨Sum.inr u, h⟩ => absurd h (hnotE u)
    refine ⟨n, fun i => φ (z i), c', hw, ?_, ?_⟩
    · rintro ⟨(l | u), h⟩
      · refine hstalkT l hw _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
        · exact (hmem (D l) (hc ⟨l, hTsub' l h⟩) p).1 (hTsub l hp)
        · refine subset_closure ⟨(hmem (D l) (hc ⟨l, hTsub' l h⟩) p).2 hp, fun hZ' => ?_⟩
          exact (hgen p).mem_open ((Z.support.isClosed.isOpen_compl).preimage π.continuous) hx
            hZ'
      · exact absurd h (hnotE u)
    · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
      · have := hinj hab
        simp only [Subtype.mk.injEq] at this
        subst this
        rfl
      · exact absurd hb (hnotE v)
      · exact absurd ha (hnotE u)
      · exact absurd ha (hnotE u)

/-- The blow-up of a centre having snc with an snc divisor, for a base locally of finite type over
a perfect field. -/
private theorem isSNCFamily_blowUpTransformFamily_of_locallyOfFiniteType {k : Type u}
    [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {Λ : Type*}
    {D : Λ → Y.IdealSheafData} (hD : IsSNCFamily sY D) {Z : Y.IdealSheafData}
    (hZ : HasSNCWith D Z) : IsSNCFamily (blowUpToBase Z ≫ sY) (blowUpTransformFamily D Z) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have hpar : ∀ i, ∀ y ∈ (blowUpTransformFamily D Z i).support,
      ∃ (m : ℕ) (w : Fin m → (blowUp Z).presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (blowUpTransformFamily D Z i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ :=
      exists_coordinates_blowUpTransformFamily_of_isLocallyNoetherian hD hZ y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  refine ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, fun y => ?_⟩
  exact exists_coordinates_blowUpTransformFamily_of_isLocallyNoetherian hD hZ y

/-- The exceptional divisor with the strict transforms is snc. -/
private theorem isSNCFamily_blowUp_componentsFamily_inter {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [Smooth sY] {Λ : Type*}
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) :
    let Z := componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W
    let π := blowUpToBase Z
    let D : Option Λ → (blowUp Z).IdealSheafData := fun
      | none => Z.comap π
      | some j => Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))
    IsSNCFamily (π ≫ sY) D := by
  intro Z π D
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hsupp : (Z.support : Set Y) = W :=
    coe_support_componentsFamily (((H i₁).support.isClosed).inter (H i₂).support.isClosed) W
  have hZ : HasSNCWith H Z := by
    intro x hx
    rw [hsupp] at hx
    obtain ⟨n, z, c, s, -, hz, hc, hinj, hs⟩ :=
      exists_stalk_componentsFamily_inter_eq sY H hH hne W x hx
    exact ⟨n, z, c, s, hz, hc, hinj, hs⟩
  have h := isSNCFamily_blowUpTransformFamily_of_locallyOfFiniteType sY hH hZ
  have hD : D = blowUpTransformFamily H Z ∘ (fun o => Option.elim o (Sum.inr ()) Sum.inl) := by
    funext o
    cases o with
    | none => rfl
    | some j =>
      change Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y)))) = _
      simp only [Function.comp_apply, Option.elim_some, blowUpTransformFamily, Sum.elim_inl]
      rw [hsupp]
  rw [hD]
  refine h.comp _ ?_
  rintro (_ | a) (_ | b) hab
  · rfl
  · exact absurd hab Sum.inr_ne_inl
  · exact absurd hab Sum.inl_ne_inr
  · exact congrArg some (Sum.inl_injective hab)

/-- Let `f : B → Y` restrict to an open embedding of `f⁻¹(U)`, `U` open, and let `K ⊆ B` be closed
with `K ∩ f⁻¹(U) = f⁻¹(T ∩ U)`. Every component of `K` meeting `f⁻¹(U)` is the closure of the
inverse image of `V ∩ U` for a component `V` of `T` meeting `U`. -/
private theorem exists_mem_componentsOf_eq_closure_preimage_inter {B Y : Type*}
    [TopologicalSpace B] [TopologicalSpace Y] [QuasiSober B]
    {f : B → Y} {U : Set Y} (hO : IsOpen (f ⁻¹' U))
    (hg : Topology.IsOpenEmbedding ((f ⁻¹' U).restrict f)) {T : Set Y} {K : Set B}
    (hK : IsClosed K) (hKT : K ∩ f ⁻¹' U = f ⁻¹' (T ∩ U)) {C : Set B} (hC : C ∈ componentsOf K)
    (hCU : (C ∩ f ⁻¹' U).Nonempty) :
    ∃ V ∈ componentsOf T, (V ∩ U).Nonempty ∧ C = closure (f ⁻¹' (V ∩ U)) := by
  have hCcl : IsClosed C := Aux.isClosed_of_mem_componentsOf hK hC
  have hξ := hC.1.1.isGenericPoint_genericPoint_closure
  rw [hCcl.closure_eq] at hξ
  set ξ := hC.1.1.genericPoint
  have hξO : ξ ∈ f ⁻¹' U := (hξ.mem_open_set_iff hO).2 hCU
  have hξT : f ξ ∈ T := by
    have : ξ ∈ f ⁻¹' (T ∩ U) := hKT ▸ ⟨hC.1.2 hξ.mem, hξO⟩
    exact this.1
  obtain ⟨V, hV, hξV⟩ := exists_mem_componentsOf hξT
  have hG : f ⁻¹' (V ∩ U) = Subtype.val '' ((f ⁻¹' U).restrict f ⁻¹' V) := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
  have hξG : ξ ∈ f ⁻¹' (V ∩ U) := ⟨hξV, hξO⟩
  have hGirr : IsIrreducible (f ⁻¹' (V ∩ U)) := by
    refine ⟨⟨ξ, hξG⟩, ?_⟩
    rw [hG]
    exact (hV.1.1.2.preimage hg).image _ continuous_subtype_val.continuousOn
  have hGK : closure (f ⁻¹' (V ∩ U)) ⊆ K := by
    refine closure_minimal (fun x hx => ?_) hK
    have : x ∈ f ⁻¹' (T ∩ U) := ⟨hV.1.2 hx.1, hx.2⟩
    rw [← hKT] at this
    exact this.1
  have hCG : C ⊆ closure (f ⁻¹' (V ∩ U)) := by
    rw [← hξ.def]
    exact closure_mono (Set.singleton_subset_iff.2 hξG)
  refine ⟨V, hV, ⟨f ξ, hξV, hξO⟩, ?_⟩
  exact hCG.antisymm (hC.2 ⟨hGirr.closure, hGK⟩ hCG)

/-- Every component of `H'_i ∩ H'_j`, `i ≠ j`, is the
strict transform of a component `V ≠ W` of `H_i ∩ H_j`. -/
private theorem exists_eq_closure_preimage_of_mem_componentsOf_strictTransform {k : Type u}
    [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] {Λ : Type*}
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) (Z : Y.IdealSheafData)
    (hZdef : Z = componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W) {i j : Λ}
    (hij : i ≠ j) (C : Set (blowUp Z))
    (hC : C ∈ componentsOf (closure (blowUpToBase Z ⁻¹' ((H i).support \ (W : Set Y))) ∩
        closure (blowUpToBase Z ⁻¹' ((H j).support \ (W : Set Y))))) :
    ∃ V ∈ componentsOf ((H i).support ∩ (H j).support : Set Y),
      V ≠ (W : Set Y) ∧ C = closure (blowUpToBase Z ⁻¹' (V \ (W : Set Y))) := by
  set π := blowUpToBase Z
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian (blowUp Z) := LocallyOfFiniteType.isLocallyNoetherian π
  have hsupp : (Z.support : Set Y) = W := hZdef ▸
    coe_support_componentsFamily (((H i₁).support.isClosed).inter (H i₂).support.isClosed) W
  let D : Option Λ → (blowUp Z).IdealSheafData := fun
    | none => Z.comap π
    | some j => Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))
  have hsnc : IsSNCFamily (π ≫ sY) D := by
    subst hZdef; exact isSNCFamily_blowUp_componentsFamily_inter sY H hH hne W
  have hS : ∀ j, ((D (some j)).support : Set (blowUp Z)) =
      closure (π ⁻¹' ((H j).support \ (W : Set Y))) := fun j => by
    change ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))).support : Set (blowUp Z)) = _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hE : ((D none).support : Set (blowUp Z)) = π ⁻¹' (W : Set Y) := by
    change ((Z.comap π).support : Set (blowUp Z)) = _
    rw [Scheme.IdealSheafData.support_comap]
    change π ⁻¹' ((Z.support : Set Y)) = _
    rw [hsupp]
  have hSsub : ∀ j, closure (π ⁻¹' ((H j).support \ (W : Set Y))) ⊆ π ⁻¹' (H j).support :=
    fun j => closure_minimal (fun y hy => hy.1) (((H j).support.isClosed).preimage π.continuous)
  have hU : IsOpen (W : Set Y)ᶜ := hsupp ▸ Z.support.isClosed.isOpen_compl
  have hg : Topology.IsOpenEmbedding ((π ⁻¹' (W : Set Y)ᶜ).restrict π) := by
    have hiso := isIso_blowUp_restrict_compl_support Z
    have h := ((π ∣_ (⟨Z.supportᶜ, Z.support.isClosed.isOpen_compl⟩ : Y.Opens)) ≫
      Scheme.Opens.ι _).isOpenEmbedding
    rw [morphismRestrict_ι] at h
    have hset : π ⁻¹' (W : Set Y)ᶜ = ((π ⁻¹ᵁ (⟨Z.supportᶜ, Z.support.isClosed.isOpen_compl⟩ :
        Y.Opens) : (blowUp Z).Opens) : Set (blowUp Z)) := by
      ext x
      change π x ∉ (W : Set Y) ↔ π x ∉ (Z.support : Set Y)
      rw [hsupp]
    exact h.comp (Homeomorph.setCongr hset).isOpenEmbedding
  have hCU : (C ∩ π ⁻¹' (W : Set Y)ᶜ).Nonempty := by
    by_contra! hne'
    refine not_subset_support_of_mem_componentsOf_inter (π ≫ sY) hsnc
      (a := some i) (b := some j) (c := none) (fun h => hij (Option.some_injective _ h))
      (by simp) (by simp) (C := C) (by rw [hS, hS]; exact hC) ?_
    intro x hx
    rw [hE]
    by_contra hxW
    exact (Set.eq_empty_iff_forall_notMem.1 hne') x ⟨hx, hxW⟩
  have hKT : (closure (π ⁻¹' ((H i).support \ (W : Set Y))) ∩
      closure (π ⁻¹' ((H j).support \ (W : Set Y)))) ∩ π ⁻¹' (W : Set Y)ᶜ =
      π ⁻¹' (((H i).support ∩ (H j).support : Set Y) ∩ (W : Set Y)ᶜ) := by
    ext x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨hSsub i h1, hSsub j h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨subset_closure ⟨h1, h3⟩, subset_closure ⟨h2, h3⟩⟩, h3⟩
  obtain ⟨V, hV, hVU, hCV⟩ := exists_mem_componentsOf_eq_closure_preimage_inter
    (hU.preimage π.continuous) hg
    ((isClosed_closure).inter isClosed_closure) hKT hC hCU
  refine ⟨V, hV, fun h => ?_, hCV⟩
  obtain ⟨y, hyV, hyW⟩ := hVU
  exact hyW (h ▸ hyV)

/-- The components of pairwise intersections of new boundary components. -/
private theorem mem_componentsOf_inter_blowUp_componentsFamily_inter {k : Type u}
    [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] {Λ : Type*}
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) :
    let Z := componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W
    let π := blowUpToBase Z
    let D : Option Λ → (blowUp Z).IdealSheafData := fun
      | none => Z.comap π
      | some j => Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))
    ∀ a b : Option Λ, a ≠ b →
        ∀ C ∈ componentsOf ((D a).support ∩ (D b).support : Set (blowUp Z)),
          (∃ i j : Λ, a = some i ∧ b = some j ∧
              ∃ V ∈ componentsOf ((H i).support ∩ (H j).support : Set Y),
                V ≠ (W : Set Y) ∧ C = closure (π ⁻¹' (V \ (W : Set Y)))) ∨
            ∃ j : Λ, ((a = none ∧ b = some j) ∨ (a = some j ∧ b = none)) ∧
              ((H j).support ∩ (W : Set Y) : Set Y).Nonempty := by
  intro Z π D a b hab C hC
  have hE : ((D none).support : Set (blowUp Z)) = π ⁻¹' (W : Set Y) := by
    change ((Z.comap π).support : Set (blowUp Z)) = _
    rw [Scheme.IdealSheafData.support_comap]
    change π ⁻¹' ((Z.support : Set Y)) = _
    rw [coe_support_componentsFamily
      (((H i₁).support.isClosed).inter (H i₂).support.isClosed) W]
  have hS : ∀ j, ((D (some j)).support : Set (blowUp Z)) =
      closure (π ⁻¹' ((H j).support \ (W : Set Y))) := fun j => by
    change ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))).support : Set (blowUp Z)) = _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hSsub : ∀ j, ((D (some j)).support : Set (blowUp Z)) ⊆ π ⁻¹' (H j).support := fun j => by
    rw [hS]
    exact closure_minimal (fun y hy => hy.1)
      (((H j).support.isClosed).preimage π.continuous)
  -- a point of the exceptional divisor on `H'_j` lies over `H_j ∩ W`
  have hmeet : ∀ j, C ⊆ ((D none).support : Set (blowUp Z)) ∩ (D (some j)).support →
      ((H j).support ∩ (W : Set Y) : Set Y).Nonempty := fun j hsub => by
    obtain ⟨y, hy⟩ := hC.1.1.nonempty
    obtain ⟨h1, h2⟩ := hsub hy
    rw [hE] at h1
    exact ⟨π y, hSsub j h2, h1⟩
  match a, b, hab, hC with
  | none, none, hab, _ => exact absurd rfl hab
  | none, some j, _, hC =>
    exact Or.inr ⟨j, Or.inl ⟨rfl, rfl⟩, hmeet j hC.1.2⟩
  | some j, none, _, hC =>
    exact Or.inr ⟨j, Or.inr ⟨rfl, rfl⟩, hmeet j (fun y hy => (hC.1.2 hy).symm)⟩
  | some i, some j, hab, hC =>
    have hij : i ≠ j := fun h => hab (h ▸ rfl)
    rw [hS i, hS j] at hC
    exact Or.inl ⟨i, j, rfl, rfl, exists_eq_closure_preimage_of_mem_componentsOf_strictTransform
      sY H hH hne W Z rfl hij C hC⟩

/-- **Blowing up a component of a double intersection of an snc divisor.** Let `Y` be smooth
over a perfect field `k` with an snc divisor `∑_j H_j`, and let `W` be an irreducible component of
`H_k ∩ H_l`, `k ≠ l`, with its reduced structure. Then the blow-up `π : B_W Y → Y` is smooth
over `k`. The exceptional divisor together with the strict transforms
`H'_j = π⁻¹(H_j ∖ W)‾` is snc. Every irreducible component `C` of the intersection of two
distinct new boundary components is either the strict transform `π⁻¹(V ∖ W)‾` of a component
`V ≠ W` of `H_i ∩ H_j`, where the two components are `H'_i` and `H'_j`, or a component of
`E ∩ H'_j` with `H_j ∩ W ≠ ∅`. -/
@[mmp "lem_mmp_blowup_snc_pair_stratum"]
public theorem blowUp_snc_pair_stratum {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] {Λ : Type*} [Finite Λ]
    (H : Λ → Y.IdealSheafData) (hH : IsSNCFamily sY H) {i₁ i₂ : Λ} (hne : i₁ ≠ i₂)
    (W : componentsOf ((H i₁).support ∩ (H i₂).support : Set Y)) :
    let Z := componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W
    let π := blowUpToBase Z
    let D : Option Λ → (blowUp Z).IdealSheafData := fun
      | none => Z.comap π
      | some j => Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (π ⁻¹' ((H j).support \ (W : Set Y))))
    Smooth (π ≫ sY) ∧ IsSNCFamily (π ≫ sY) D ∧
      ∀ a b : Option Λ, a ≠ b →
        ∀ C ∈ componentsOf ((D a).support ∩ (D b).support : Set (blowUp Z)),
          (∃ i j : Λ, a = some i ∧ b = some j ∧
              ∃ V ∈ componentsOf ((H i).support ∩ (H j).support : Set Y),
                V ≠ (W : Set Y) ∧ C = closure (π ⁻¹' (V \ (W : Set Y)))) ∨
            ∃ j : Λ, ((a = none ∧ b = some j) ∨ (a = some j ∧ b = none)) ∧
              ((H j).support ∩ (W : Set Y) : Set Y).Nonempty :=
  ⟨smooth_blowUp_componentsFamily_inter sY H hH hne W,
    isSNCFamily_blowUp_componentsFamily_inter sY H hH hne W,
    mem_componentsOf_inter_blowUp_componentsFamily_inter sY H hH hne W⟩

end MMP.Resolution

/-! ### Pushforward of the structure sheaf under a field extension -/

namespace MMP.Foundations

open CategoryTheory Limits AlgebraicGeometry

private lemma isIso_of_isPushout_of_faithfullyFlat {A B A' B' : CommRingCat.{u}} {φ : A ⟶ B}
    {ψ : A ⟶ A'} {φ' : B ⟶ B'} {χ : A' ⟶ B'} (h : IsPushout φ ψ φ' χ)
    (hψ : ψ.hom.FaithfullyFlat) [IsIso χ] : IsIso φ := by
  algebraize [φ.hom, ψ.hom, χ.hom, φ'.hom, (φ ≫ φ').hom]
  have : IsScalarTower A B B' := .of_algebraMap_eq' rfl
  have : IsScalarTower A A' B' := .of_algebraMap_eq' congr(($h.w).hom)
  have : Algebra.IsPushout A B A' B' := (CommRingCat.isPushout_iff_isPushout.mp h.flip).symm
  exact (RingEquiv.ofBijective φ.hom (hψ.codescendsAlong_bijective
    (R := A) (S := B) (R' := A') (S' := B') (ConcreteCategory.bijective_of_isIso χ))
    ).toCommRingCatIso.isIso_hom

private lemma isIso_app_of_isBasis {X Z : Scheme.{u}} (f : X ⟶ Z) {ι : Type*} {B : ι → Z.Opens}
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B)) (h : ∀ i, IsIso (f.app (B i)))
    (U : Z.Opens) : IsIso (f.app U) := by
  let φ : Z.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.base).obj X.sheaf := ⟨f.c⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB fun i ↦ h i
  have : IsIso φ.hom := @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) φ this
  exact NatIso.isIso_app_of_isIso φ.hom (Opposite.op U)

/-- The affine opens of `T` lying over an affine open of `S` form a basis of `T`. -/
private lemma isBasis_affineOpens_le_preimage {S T : Scheme.{u}} (g : T ⟶ S) :
    TopologicalSpace.Opens.IsBasis (Set.range fun W : {W : T.affineOpens //
      ∃ U : S.affineOpens, (W : T.Opens) ≤ g ⁻¹ᵁ U} ↦ (W.1 : T.Opens)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro O x hx
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T.isBasis_affineOpens (U := O ⊓ g ⁻¹ᵁ U) ⟨hx, hxU⟩
  exact ⟨W, ⟨⟨⟨W, hW⟩, ⟨U, hU⟩, hWle.trans inf_le_right⟩, rfl⟩, hxW, hWle.trans inf_le_left⟩

/-- Base change of a morphism `f : X ⟶ Z` over `S` along `s : T ⟶ S` gives a cartesian square
over `f`. -/
private lemma isPullback_pullbackMap {X Z S T : Scheme.{u}} (p : X ⟶ S) (q : Z ⟶ S)
    (s : T ⟶ S) (f : X ⟶ Z) (hf : f ≫ q = p) :
    IsPullback (pullback.fst p s) (pullback.map p s q s f (𝟙 _) (𝟙 _) (by simp [hf]) (by simp))
      f (pullback.fst q s) := by
  refine (IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback q s).flip).flip
  rw [pullback.lift_snd, Category.comp_id, hf]
  exact (IsPullback.of_hasPullback p s).flip

/-- In a cartesian square, the preimage of an open lying over `US` lies over the preimage
of `US`. -/
private lemma preimage_le_preimage_of_isPullback {X Y S T : Scheme.{u}} {fT : T ⟶ S}
    {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T} (H : IsPullback g iY iX fT) {US : S.Opens}
    {UT : T.Opens} (hle : UT ≤ fT ⁻¹ᵁ US) : iY ⁻¹ᵁ UT ≤ g ⁻¹ᵁ (iX ⁻¹ᵁ US) := by
  rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hle hx

/-- Flat base change of sections over affine opens, as a pushout square of section rings. -/
private lemma isPushout_app_of_isPullback {X Y S T : Scheme.{u}} {fT : T ⟶ S}
    {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T} (H : IsPullback g iY iX fT) [Flat fT]
    [QuasiCompact iX] [QuasiSeparated iX] {US : S.Opens} (hUS : IsAffineOpen US)
    {UT : T.Opens} (hUT : IsAffineOpen UT) (hle : UT ≤ fT ⁻¹ᵁ US) :
    IsPushout (iX.app US) (fT.appLE US UT hle)
      (g.appLE (iX ⁻¹ᵁ US) (iY ⁻¹ᵁ UT) (preimage_le_preimage_of_isPullback H hle))
      (iY.app UT) := by
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hle le_rfl
    (UY := iY ⁻¹ᵁ UT) (inf_eq_right.mpr (preimage_le_preimage_of_isPullback H hle)).symm hUS hUT
    (iX.isCompact_preimage hUS.isCompact) (iX.isQuasiSeparated_preimage hUS.isQuasiSeparated)
  rw [isIso_pushoutSection_iff] at this
  simpa only [Scheme.Hom.app_eq_appLE] using this

private lemma faithfullyFlat_appTop_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.FaithfullyFlat) : (Spec.map φ).appTop.hom.FaithfullyFlat := by
  have e : (Spec.map φ).appTop = ((Scheme.ΓSpecIso R).hom ≫ φ) ≫ (Scheme.ΓSpecIso S).inv := by
    rw [Category.assoc, Scheme.ΓSpecIso_inv_naturality]; simp
  rw [e, CommRingCat.hom_comp, RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso,
    CommRingCat.hom_comp, RingHom.FaithfullyFlat.respectsIso.cancel_left_isIso]
  exact hφ

private lemma faithfullyFlat_appLE_of_isPullback {X Y S T : Scheme.{u}} {fT : T ⟶ S}
    {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T} (H : IsPullback g iY iX fT) [IsAffine S]
    [IsAffine T] (hf : fT.appTop.hom.FaithfullyFlat) {UX : X.Opens} (hUX : IsAffineOpen UX) :
    (g.appLE UX (g ⁻¹ᵁ UX) le_rfl).hom.FaithfullyFlat := by
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := UX)
    (UY := g ⁻¹ᵁ UX) (by simp) (by simp) (by simp) (isAffineOpen_top S) (isAffineOpen_top T) hUX
  replace this := (isIso_pushoutSection_iff _ _ _ _).mp this
  rw [← this.inl_isoPushout_inv, CommRingCat.hom_comp,
    RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hf
  exact RingHom.FaithfullyFlat.isStableUnderBaseChange.pushout_inl
    RingHom.FaithfullyFlat.respectsIso _ _ hf

/-- For a qcqs morphism of `k`-schemes `f : X ⟶ Z` and a field extension `k ⊆ K`, with base change
`f_K : X_K ⟶ Z_K`, one has `f_* 𝒪_X = 𝒪_Z` if and only if `(f_K)_* 𝒪_{X_K} = 𝒪_{Z_K}`. -/
public theorem isIso_app_iff_isIso_baseChange_app
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) (q : Z ⟶ Spec (.of k))
    (f : X ⟶ Z) (hf : f ≫ q = p) [QuasiCompact f] [QuasiSeparated f] :
    (∀ U : Z.Opens, IsIso (f.app U)) ↔
      ∀ U : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
        IsIso ((pullback.map p (Spec.map (CommRingCat.ofHom (algebraMap k K))) q
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) f (𝟙 _) (𝟙 _)
          (by simp [hf]) (by simp)).app U) := by
  set s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have H := isPullback_pullbackMap p q s f hf
  have : IsAffineHom (pullback.fst q s) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q s).flip
      inferInstance
  constructor
  · intro h
    refine isIso_app_of_isBasis _ (isBasis_affineOpens_le_preimage (pullback.fst q s)) ?_
    rintro ⟨⟨W, hW⟩, ⟨U, hU⟩, hle⟩
    exact (isPushout_app_of_isPullback H hU hW hle).isIso_inr_of_isIso (h U)
  · intro h
    refine isIso_app_of_isBasis f (B := fun U : Z.affineOpens ↦ U) (by simpa using
      Z.isBasis_affineOpens) ?_
    rintro ⟨U, hU⟩
    have := h (pullback.fst q s ⁻¹ᵁ U)
    exact isIso_of_isPushout_of_faithfullyFlat
      (isPushout_app_of_isPullback H hU (hU.preimage _) le_rfl)
      (faithfullyFlat_appLE_of_isPullback (IsPullback.of_hasPullback q s)
        (faithfullyFlat_appTop_SpecMap _ (RingHom.faithfullyFlat_algebraMap_iff.mpr
          inferInstance)) hU)

/-- For a proper morphism `f : X ⟶ Z` of schemes of finite type over a field `k` and a field
extension `k ⊆ K`, with base change `f_K : X_K ⟶ Z_K`: over every affine open `U ⊆ Z` and affine
open `W ⊆ Z_K` lying over `U`, the square of section rings formed by `f`, `f_K` and the two
projections is a pushout (so `(f_* 𝒪_X) ⊗_k K ≅ (f_K)_* 𝒪_{X_K}` via the base change map), and
`f_* 𝒪_X = 𝒪_Z` if and only if `(f_K)_* 𝒪_{X_K} = 𝒪_{Z_K}`. -/
@[mmp "lem_mmp_foundation_field_extension_pushforward"]
public theorem isPushout_app_pullbackMap_and_isIso_app_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q : Z ⟶ Spec (.of k)) [LocallyOfFiniteType q] [QuasiCompact q]
    (f : X ⟶ Z) [IsProper f] (hf : f ≫ q = p) :
    (∀ (U : Z.Opens), IsAffineOpen U →
      ∀ (W : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens),
        IsAffineOpen W →
        ∀ (hle : W ≤ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U),
          IsPushout (f.app U)
            ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE U W hle)
            ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appLE (f ⁻¹ᵁ U)
              ((pullback.map p (Spec.map (CommRingCat.ofHom (algebraMap k K))) q
                (Spec.map (CommRingCat.ofHom (algebraMap k K))) f (𝟙 _) (𝟙 _)
                (by simp [hf]) (by simp)) ⁻¹ᵁ W)
              (by
                refine le_trans (Scheme.Hom.preimage_mono _ hle) (le_of_eq ?_)
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.lift_fst]))
            ((pullback.map p (Spec.map (CommRingCat.ofHom (algebraMap k K))) q
                (Spec.map (CommRingCat.ofHom (algebraMap k K))) f (𝟙 _) (𝟙 _)
                (by simp [hf]) (by simp)).app W)) ∧
    ((∀ U : Z.Opens, IsIso (f.app U)) ↔
      ∀ U : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
        IsIso ((pullback.map p (Spec.map (CommRingCat.ofHom (algebraMap k K))) q
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) f (𝟙 _) (𝟙 _)
          (by simp [hf]) (by simp)).app U)) := by
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  exact ⟨fun _ hU _ hW hle ↦
      isPushout_app_of_isPullback (isPullback_pullbackMap p q _ f hf) hU hW hle,
    isIso_app_iff_isIso_baseChange_app p q f hf⟩

end MMP.Foundations

/-! ### Points isolated in their fibre -/

namespace MMP

open AlgebraicGeometry CategoryTheory

/-- A point is open in its scheme-theoretic fibre iff it is isolated in its set-theoretic
fibre in the topology of `X`. -/
private lemma isOpen_singleton_asFiber_iff {X Y : Scheme} (f : X ⟶ Y) (x : X) :
    IsOpen {f.asFiber x} ↔ ∃ U : Set X, IsOpen U ∧ U ∩ f ⁻¹' {f x} = {x} := by
  have hx : (f.fiberHomeo (f x)) '' {f.asFiber x} = Subtype.val ⁻¹' {x} := by
    ext ⟨z, hz⟩
    simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply,
      Set.mem_singleton_iff, Subtype.ext_iff, Set.mem_preimage]
  rw [← (f.fiberHomeo (f x)).isOpen_image, hx, isOpen_induced_iff]
  refine exists_congr fun U => and_congr_right fun _ => ?_
  rw [Subtype.preimage_coe_eq_preimage_coe_iff,
    (Set.inter_eq_right (s := f ⁻¹' {f x}) (t := {x})).2
      (by simp only [Set.singleton_subset_iff, Set.mem_preimage, Set.mem_singleton_iff]),
    Set.inter_comm]

/-- For a morphism `φ : X ⟶ P` of schemes of finite type over a Noetherian scheme `S`, the set of
points `x : X` isolated in their fibre `φ⁻¹(φ x)` is open in `X`. -/
@[mmp "lem_mmp_foundation_isolated_fibre_point_locus_open"]
public theorem isOpen_setOf_isolated_mem_fiber {S X P : Scheme.{u}} [IsNoetherian S]
    (p : X ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p]
    (q : P ⟶ S) [LocallyOfFiniteType q] [QuasiCompact q]
    (φ : X ⟶ P) (hφ : φ ≫ q = p) :
    IsOpen {x : X | ∃ U : Set X, IsOpen U ∧ U ∩ φ ⁻¹' {φ x} = {x}} := by
  subst hφ
  have := locallyOfFiniteType_of_comp φ q
  simpa only [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber,
    isOpen_singleton_asFiber_iff] using φ.isOpen_quasiFiniteAt

end MMP

/-! ### An invertible top differential gives an isolated fibre point -/

namespace MMP.Intersection

open CategoryTheory AlgebraicGeometry KaehlerDifferential Stacks.RelativeDifferentialStalkMap
  Stacks.DeRham.FormsGenerators

/-- If the differentials `d(wᵢ)` of elements of `B` have unit determinant against a basis of
`Ω_{A/K}`, then `Ω_{A/B} = 0`. -/
private theorem subsingleton_of_isUnit_det {K B A : Type*} [CommRing K] [CommRing B]
    [CommRing A] [Algebra K B] [Algebra K A] [Algebra B A] [IsScalarTower K B A] {n : ℕ}
    (b : Module.Basis (Fin n) A Ω[A⁄K]) (w : Fin n → B)
    (hw : IsUnit (b.det fun i => D K A (algebraMap B A (w i)))) : Subsingleton Ω[A⁄B] := by
  have hspan := (b.is_basis_iff_det.mpr hw).2
  have hzero : ∀ x : Ω[A⁄K], map K B A A x = 0 := by
    intro x
    have hx : x ∈ Submodule.span A (Set.range fun i => D K A (algebraMap B A (w i))) := by
      rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simp
    | zero => simp
    | add _ _ _ _ h1 h2 => simp [h1, h2]
    | smul a _ _ h => simp [h]
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := map_surjective K B A x
  obtain ⟨y, rfl⟩ := map_surjective K B A y
  rw [hzero, hzero]

/-- Over a local ring, if a linear form takes a unit value on an element of the span of `G`,
it takes a unit value on some element of `G`. -/
private theorem exists_isUnit_of_mem_span {A N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup N] [Module A N] (F : N →ₗ[A] A) {G : Set N} {x : N}
    (hx : x ∈ Submodule.span A G) (hFx : IsUnit (F x)) : ∃ y ∈ G, IsUnit (F y) := by
  by_contra hne
  push Not at hne
  have : ∀ m ∈ Submodule.span A G, F m ∈ IsLocalRing.maximalIdeal A := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem y hy => exact (IsLocalRing.mem_maximalIdeal _).mpr (hne y hy)
    | zero => simp
    | add _ _ _ _ h1 h2 => rw [map_add]; exact Ideal.add_mem _ h1 h2
    | smul a _ _ h => rw [map_smul]; exact Ideal.mul_mem_left _ a h
  exact (IsLocalRing.mem_maximalIdeal _).mp (this x hx) hFx

/-- The linear form on `⋀ⁿ M` given by the determinant against a basis `b` of `M`. -/
private noncomputable abbrev detForm {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n : ℕ} (b : Module.Basis (Fin n) A M) : (⋀[A]^n M) →ₗ[A] A :=
  exteriorPower.alternatingMapLinearEquiv b.det

private theorem detForm_ιMulti {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n : ℕ} (b : Module.Basis (Fin n) A M) (v : Fin n → M) :
    detForm b (exteriorPower.ιMulti A n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The top wedge of a basis lies in the span of the wedges of differentials. -/
private theorem ιMulti_mem_span_D {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    (x : ⋀[A]^n Ω[A⁄R]) :
    x ∈ Submodule.span A (exteriorPower.ιMulti A n '' {v | ∃ w : Fin n → A,
      v = fun i => D R A (w i)}) := by
  have h : Submodule.span A (exteriorPower.ιMulti A n '' {a : Fin n → Ω[A⁄R] |
      Set.range a ⊆ Set.range (D R A)}) = ⊤ :=
    exteriorPower.ιMulti_span_of_span A n Ω[A⁄R] (span_range_derivation R A)
  have hsub : {a : Fin n → Ω[A⁄R] | Set.range a ⊆ Set.range (D R A)} ⊆
      {v | ∃ w : Fin n → A, v = fun i => D R A (w i)} := by
    intro a ha
    choose w hw using fun i => ha ⟨i, rfl⟩
    exact ⟨w, funext fun i => (hw i).symm⟩
  have : x ∈ Submodule.span A (exteriorPower.ιMulti A n '' {a : Fin n → Ω[A⁄R] |
      Set.range a ⊆ Set.range (D R A)}) := by rw [h]; trivial
  exact Submodule.span_mono (Set.image_mono hsub) this

/-- For a formally smooth local algebra `A` essentially of finite type, `Ω[A⁄R]` of rank `n`
has a basis indexed by `Fin n`. -/
private theorem nonempty_basis_kaehler {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [Algebra.FormallySmooth R A] [Algebra.EssFiniteType R A] {n : ℕ}
    (hn : Module.finrank A Ω[A⁄R] = n) : Nonempty (Module.Basis (Fin n) A Ω[A⁄R]) := by
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Projective A Ω[A⁄R] := ((Algebra.formallySmooth_iff R A).mp inferInstance).1
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  exact ⟨Module.finBasisOfFinrankEq _ _ hn⟩

/-- On a smooth variety `Y` of dimension `n` over a field, the module of Kähler differentials of
the local ring at `y` over the base is free of rank `n`. -/
private theorem nonempty_basis_kaehler_stalk {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [MMP.Mori.IsVariety k f] [Smooth f] {n : ℕ}
    (hn : topologicalKrullDim Y = n) (y : Y) :
    letI := algebraStalkMap f y
    Nonempty (Module.Basis (Fin n) (ToType (Y.sheaf.presheaf.stalk y))
      Ω[ToType (Y.sheaf.presheaf.stalk y)⁄ToType ((Spec (.of k)).presheaf.stalk (f y))]) := by
  letI := algebraStalkMap f y
  classical
  have : LocallyOfFiniteType f := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsLocalRing (ToType (Y.sheaf.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalRing (Y.presheaf.stalk y))
  have : Algebra.FormallySmooth (ToType ((Spec (.of k)).presheaf.stalk (f y)))
      (ToType (Y.sheaf.presheaf.stalk y)) :=
    InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f y
      (InfinitesimalLifting.smoothAt_of_smooth f y)
  have : Algebra.EssFiniteType (ToType ((Spec (.of k)).presheaf.stalk (f y)))
      (ToType (Y.sheaf.presheaf.stalk y)) := essFiniteType_stalkMap f y
  exact nonempty_basis_kaehler
    (MMP.Intersection.finrank_kaehlerDifferential_stalk_of_isVariety f hn y)

/-- If `⋀ b = c • ε` for a basis `b`, then any `n`-tuple `v` with `⋀ v = u • ε`, `u` a unit, has
unit determinant against `b`. -/
private theorem isUnit_det_of_ιMulti_eq_smul {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) {v : Fin n → M} {ε : ⋀[A]^n M} {c u : A}
    (hb : exteriorPower.ιMulti A n b = c • ε) (hv : exteriorPower.ιMulti A n v = u • ε)
    (hu : IsUnit u) : IsUnit (b.det v) := by
  have h := congrArg (detForm b) hb
  rw [detForm_ιMulti, Module.Basis.det_self, map_smul, smul_eq_mul] at h
  rw [← detForm_ιMulti, hv, map_smul, smul_eq_mul]
  exact hu.mul (isUnit_of_mul_isUnit_right (h ▸ isUnit_one))

/-- Germs of the image of a section under a map into the sheaf of `n`-forms do not change
under restriction. -/
private theorem germ_app_map {T S : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    {L : S.Modules} (φ : L ⟶ Scheme.Hom.relativeDifferentialForms f n) {s : S}
    {U₁ U₂ : S.Opens} (h : U₂ ≤ U₁) (hs₂ : s ∈ U₂) (t : Γ(L, U₁)) :
    TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf U₂ s hs₂ (φ.app U₂ (L.presheaf.map (homOfLE h).op t)) =
      TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf U₁ s (h hs₂) (φ.app U₁ t) := by
  have hn := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) t
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at hn
  rw [hn]
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE h) s hs₂ _

/-- Near a point `x`, every wedge `dw₁ ∧ ⋯ ∧ dwₙ` of stalk elements is the germ of
`d • s₀` for a trivializing generator `s₀` of `Ω^n_X`, where `d • s₀ = dw̃₁ ∧ ⋯ ∧ dw̃ₙ` for
sections `w̃ᵢ` lifting the `wᵢ`. -/
private theorem exists_gen_eq_smul_generator {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ) {V : X.Opens} {x : X} (hxV : x ∈ V)
    {s₀ : Γ(Scheme.Hom.relativeDifferentialForms sX n, V)}
    (hs₀ : IsTrivializingGenerator _ V s₀) (w : Fin n → ToType (X.sheaf.presheaf.stalk x)) :
    letI := algebraStalkMap sX x
    ∃ (V' : X.Opens) (hV' : V' ≤ V) (hxV' : x ∈ V') (wt : Fin n → Γ(X, V')) (d : Γ(X, V')),
      (∀ i, X.presheaf.germ V' x hxV' (wt i) = w i) ∧
      d • (Scheme.Hom.relativeDifferentialForms sX n).presheaf.map (homOfLE hV').op s₀ =
        gen sX V' wt ∧
      exteriorPower.ιMulti _ n (fun i => D (ToType ((Spec (.of k)).presheaf.stalk (sX x)))
        (ToType (X.sheaf.presheaf.stalk x)) (w i)) =
        X.sheaf.presheaf.germ V' x hxV' d • formsStalkEquiv sX n x (TopCat.Presheaf.germ
          ((Scheme.Hom.relativeDifferentials sX).exteriorAlgebra.piece (n : ℤ)).val.presheaf
            V x hxV s₀) := by
  letI := algebraStalkMap sX x
  obtain ⟨V₁, hx₁, wt₁, hwt₁⟩ := exists_germ_eq_of_fin x w
  have hx' : x ∈ V ⊓ V₁ := ⟨hxV, hx₁⟩
  let wt : Fin n → Γ(X, V ⊓ V₁) := fun i => X.presheaf.map (homOfLE inf_le_right).op (wt₁ i)
  obtain ⟨d, hd⟩ := (hs₀ (V ⊓ V₁) inf_le_left).2 (gen sX (V ⊓ V₁) wt)
  have hwt : ∀ i, X.presheaf.germ (V ⊓ V₁) x hx' (wt i) = w i := fun i =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hwt₁ i)
  refine ⟨V ⊓ V₁, inf_le_left, hx', wt, d, hwt, hd, ?_⟩
  have h1 := formsStalkEquiv_germ_smul sX hx' n d
    ((Scheme.Hom.relativeDifferentialForms sX n).presheaf.map (homOfLE inf_le_left).op s₀)
  rw [show d • _ = gen sX (V ⊓ V₁) wt from hd, formsStalkEquiv_germ_gen sX hx' wt] at h1
  simp only [hwt] at h1
  exact h1.trans (congrArg (_ • formsStalkEquiv sX n x ·) (TopCat.Presheaf.germ_res_apply
    ((Scheme.Hom.relativeDifferentials sX).exteriorAlgebra.piece (n : ℤ)).val.presheaf
    (homOfLE inf_le_left) x hx' s₀))

/-- If a map `φ : L ⟶ Ω^n` from a module trivialized by `e` near `s` is surjective on stalks
at `s`, then every element of `(Ω^n)_s` is a multiple of the germ of `φ(e)`. -/
private theorem exists_eq_germ_smul_of_surjective {T S : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    {L : S.Modules} (φ : L ⟶ Scheme.Hom.relativeDifferentialForms f n) {U : S.Opens}
    {e : Γ(L, U)} (he : IsTrivializingGenerator L U e) {s : S} (hsU : s ∈ U)
    (hs : Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab.{u} s).map
      ((Scheme.Modules.toPresheaf S).map φ))) :
    letI := algebraStalkMap f s
    ∀ x : ⋀[ToType (S.sheaf.presheaf.stalk s)]^n
        Ω[ToType (S.sheaf.presheaf.stalk s)⁄ToType (T.presheaf.stalk (f s))],
      ∃ (W : S.Opens) (hsW : s ∈ W) (c : Γ(S, W)), x = S.sheaf.presheaf.germ W s hsW c •
        formsStalkEquiv f n s (TopCat.Presheaf.germ
          ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece (n : ℤ)).val.presheaf
            U s hsU (φ.app U e)) := by
  letI := algebraStalkMap f s
  intro x
  obtain ⟨ℓ, hℓ⟩ := hs ((formsStalkEquiv f n s).symm x)
  obtain ⟨W, hsW, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ ℓ
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hℓ
  have hsW' : s ∈ W ⊓ U := ⟨hsW, hsU⟩
  obtain ⟨c, hc⟩ := (he (W ⊓ U) inf_le_right).2 (L.presheaf.map (homOfLE inf_le_left).op m)
  refine ⟨W ⊓ U, hsW', c, ?_⟩
  have h0 := congrArg (formsStalkEquiv f n s) hℓ
  rw [LinearEquiv.apply_symm_apply] at h0
  rw [← h0]
  have h3 := formsStalkEquiv_germ_smul f hsW' n c
    (φ.app (W ⊓ U) (L.presheaf.map (homOfLE inf_le_right).op e))
  have e1 := (Scheme.Modules.Hom.app_smul φ c (L.presheaf.map (homOfLE inf_le_right).op e)).symm
  have e2 : c • L.presheaf.map (homOfLE inf_le_right).op e =
      L.presheaf.map (homOfLE inf_le_left).op m := hc
  have e3 := germ_app_map _ _ φ inf_le_left hsW' m
  have e4 := germ_app_map _ _ φ inf_le_right hsW' e
  have e5 : φ.app (W ⊓ U) (L.presheaf.map (homOfLE inf_le_left).op m) =
      c • φ.app (W ⊓ U) (L.presheaf.map (homOfLE inf_le_right).op e) :=
    (congrArg (φ.app (W ⊓ U)) e2.symm).trans e1.symm
  refine (congrArg (formsStalkEquiv f n s) ?_).trans (h3.trans
    (congrArg (_ • formsStalkEquiv f n s ·) e4))
  exact e3.symm.trans (congrArg (TopCat.Presheaf.germ
    ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece (n : ℤ)).val.presheaf
      (W ⊓ U) s hsW') e5)

/-- If `g : S ⟶ X` is a morphism of smooth `k`-varieties of the same dimension `n` and the
pull-back of top forms `g^*Ω^n_X ⟶ Ω^n_S` is surjective on stalks at `s`, then `s` is an isolated
point of its fibre. -/
@[mmp "lem_mmp_foundation_invertible_top_differential_isolated_fibre"]
public theorem isOpen_singleton_asFiber_of_surjective_stalk_jacobianSection
    {k : Type u} [Field k] {S X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)
    [MMP.Mori.IsVariety k sX] [MMP.Mori.IsVariety k (g ≫ sX)]
    [Smooth sX] [Smooth (g ≫ sX)] (n : ℕ)
    (hX : topologicalKrullDim X = n) (hS : topologicalKrullDim S = n) (s : S)
    (hs : Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab.{u} s).map
      ((Scheme.Modules.toPresheaf S).map (jacobianSection sX g n)))) :
    IsOpen ({g.asFiber s} : Set (g.fiber (g s))) := by
  classical
  have : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sX
  suffices hsub : Subsingleton (Stacks.SmoothAtJacobian.relativeDifferentialStalk g s) from
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp
      (quasiFiniteAt_of_unramifiedAt g
        (unramifiedAt_of_subsingleton_relativeDifferentialStalk g hsub)).2
  letI iS : Algebra (ToType ((Spec (.of k)).presheaf.stalk ((g ≫ sX) s)))
      (ToType (S.sheaf.presheaf.stalk s)) := algebraStalkMap (g ≫ sX) s
  letI iG : Algebra (ToType (X.presheaf.stalk (g s))) (ToType (S.sheaf.presheaf.stalk s)) :=
    algebraStalkMap g s
  letI iX' : Algebra (ToType ((Spec (.of k)).presheaf.stalk ((g ≫ sX) s)))
      (ToType (X.presheaf.stalk (g s))) := algebraStalkMap sX (g s)
  haveI : IsScalarTower (ToType ((Spec (.of k)).presheaf.stalk ((g ≫ sX) s)))
      (ToType (X.presheaf.stalk (g s))) (ToType (S.sheaf.presheaf.stalk s)) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change ((g ≫ sX).stalkMap s).hom r = (g.stalkMap s).hom ((sX.stalkMap (g s)).hom r)
      rw [Scheme.Hom.stalkMap_comp]
      rfl
  suffices hΩ : Subsingleton
      Ω[ToType (S.sheaf.presheaf.stalk s)⁄ToType (X.presheaf.stalk (g s))] from
    (relativeDifferentialsStalkKaehlerEquiv g s).toEquiv.subsingleton
  obtain ⟨bS⟩ := nonempty_basis_kaehler_stalk (g ≫ sX) hS s
  suffices hw : ∃ w : Fin n → ToType (X.presheaf.stalk (g s)),
      IsUnit (bS.det fun i => D _ _ (algebraMap _ (ToType (S.sheaf.presheaf.stalk s)) (w i))) by
    obtain ⟨w, hw⟩ := hw
    exact subsingleton_of_isUnit_det bS w hw
  -- trivialize `Ω^n_X` near `g s`
  have := smoothOfRelativeDimension_of_isVariety sX n hX
  have hinvX := Stacks.Discriminant.isInvertible_relativeDifferentialForms sX n
  have hLX := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := X.toRingedSpace)
    (Scheme.Hom.relativeDifferentialForms sX n) (h := hinvX)
  have : Stacks.Ample.IsInvertibleModule X (Scheme.Hom.relativeDifferentialForms sX n) := hinvX
  obtain ⟨V, -, s₀, hxV, hs₀⟩ := exists_isTrivializingGenerator
    (Scheme.Hom.relativeDifferentialForms sX n) (V := ⊤) (TopologicalSpace.Opens.mem_top (g s))
  letI iX : Algebra (ToType ((Spec (.of k)).presheaf.stalk (sX (g s))))
      (ToType (X.sheaf.presheaf.stalk (g s))) := algebraStalkMap sX (g s)
  obtain ⟨bX⟩ := nonempty_basis_kaehler_stalk sX hX (g s)
  -- some `w` has a unit coefficient `d` against the generator
  obtain ⟨y, ⟨v, ⟨w, rfl⟩, rfl⟩, hyu⟩ := exists_isUnit_of_mem_span (detForm bX)
    (ιMulti_mem_span_D (exteriorPower.ιMulti _ n bX))
    (by rw [detForm_ιMulti, Module.Basis.det_self]; exact isUnit_one)
  obtain ⟨V', hV', hxV', wt, d, hwt, hd, hιw⟩ := exists_gen_eq_smul_generator sX n hxV hs₀ w
  have hdu : IsUnit (X.sheaf.presheaf.germ V' (g s) hxV' d) := by
    rw [hιw, map_smul, smul_eq_mul] at hyu
    exact isUnit_of_mul_isUnit_left hyu
  -- the pulled-back generator upstairs
  let s₁ := (Scheme.Hom.relativeDifferentialForms sX n).presheaf.map (homOfLE hV').op s₀
  let e₀ := Stacks.SheafOfModules.pullbackGenerator g _ hLX V' ⟨s₁, hs₀.res hV'⟩
  let L := (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentialForms sX n)
  have he₀ : IsTrivializingGenerator L (g ⁻¹ᵁ V') e₀.val := e₀.2
  let φ := jacobianSection sX g n
  have hφ : g.app V' d • φ.app (g ⁻¹ᵁ V') e₀.val =
      gen (g ≫ sX) (g ⁻¹ᵁ V') fun i => g.app V' (wt i) := by
    rw [← MMP.Intersection.jacobianSection_app_pullbackUnit_gen, ← hd]
    refine Eq.trans ?_ (congrArg (φ.app (g ⁻¹ᵁ V')) (Stacks.RingedSpace.pullbackUnit_smul
      g.toLRSHom.toShHom (Scheme.Hom.relativeDifferentialForms sX n) (Opposite.op V') d s₁)).symm
    exact (Scheme.Modules.Hom.app_smul φ (g.app V' d) e₀.val).symm
  have hsV' : s ∈ g ⁻¹ᵁ V' := hxV'
  let ε := formsStalkEquiv (g ≫ sX) n s (TopCat.Presheaf.germ
    ((Scheme.Hom.relativeDifferentials (g ≫ sX)).exteriorAlgebra.piece (n : ℤ)).val.presheaf
      (g ⁻¹ᵁ V') s hsV' (φ.app (g ⁻¹ᵁ V') e₀.val))
  -- the pulled-back wedge is a unit multiple of `ε`
  have hιS : exteriorPower.ιMulti _ n (fun i => D (ToType ((Spec (.of k)).presheaf.stalk
      ((g ≫ sX) s))) (ToType (S.sheaf.presheaf.stalk s)) (g.stalkMap s (w i))) =
      S.sheaf.presheaf.germ (g ⁻¹ᵁ V') s hsV' (g.app V' d) • ε := by
    have h1 := formsStalkEquiv_germ_smul (g ≫ sX) hsV' n (g.app V' d)
      (φ.app (g ⁻¹ᵁ V') e₀.val)
    rw [hφ, formsStalkEquiv_germ_gen (g ≫ sX) hsV'] at h1
    refine Eq.trans ?_ h1
    refine congrArg (exteriorPower.ιMulti _ n) (funext fun i => congrArg (D _ _) ?_)
    rw [← hwt i]
    exact Scheme.Hom.germ_stalkMap_apply g V' s hxV' (wt i)
  -- surjectivity: the top wedge of `bS` is a multiple of `ε`
  obtain ⟨W, hsW, c, hb⟩ := exists_eq_germ_smul_of_surjective _ n φ he₀ hsV' hs
    (exteriorPower.ιMulti _ n bS)
  refine ⟨w, isUnit_det_of_ιMulti_eq_smul bS hb hιS ?_⟩
  exact (Scheme.Hom.germ_stalkMap_apply g V' s hxV' d) ▸ hdu.map (g.stalkMap s).hom

end MMP.Intersection

/-! ### Fractional parts of a tail of an irrational progression -/

namespace MMP.Foundation

/-- If `0 < |δ| < 1`, then for every `c` the fractional parts of `c + j * δ`, `j : ℕ`, come
within distance `|δ|` of every point of `[0, 1]`. -/
private lemma exists_nat_abs_fract_add_mul_sub_le (c δ y : ℝ) (hδ0 : δ ≠ 0) (hδ1 : |δ| < 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : ∃ j : ℕ, |Int.fract (c + j * δ) - y| ≤ |δ| := by
  obtain ⟨hy0, hy1⟩ := hy
  set d := |δ| with hd
  have hdpos : 0 < d := abs_pos.mpr hδ0
  set y' := min y (1 - d) with hy'
  have hy'0 : 0 ≤ y' := le_min hy0 (by linarith)
  have hy'd : y' + d ≤ 1 := by have := min_le_right y (1 - d); linarith
  have hyy' : y' ≤ y := min_le_left _ _
  suffices ∃ j : ℕ, y' ≤ Int.fract (c + j * δ) ∧ Int.fract (c + j * δ) < y' + d by
    obtain ⟨j, h1, h2⟩ := this
    refine ⟨j, abs_sub_le_iff.mpr ⟨by linarith, ?_⟩⟩
    rcases le_total y (1 - d) with h | h
    · rw [hy', min_eq_left h] at h1; linarith
    · rw [hy', min_eq_right h] at h1 h2; linarith [Int.fract_lt_one (c + j * δ)]
  have hfl := Int.floor_le c
  have hfl' := Int.lt_floor_add_one c
  rcases lt_or_gt_of_ne hδ0 with hneg | hpos
  · have hdd : d = -δ := abs_of_neg hneg
    have harg : 0 ≤ (c - ⌊c⌋ - y' + 1) / d := div_nonneg (by linarith) hdpos.le
    set j := ⌊(c - ⌊c⌋ - y' + 1) / d⌋₊
    have h1 := Nat.floor_le harg
    have h2 := Nat.lt_floor_add_one ((c - ⌊c⌋ - y' + 1) / d)
    rw [le_div_iff₀ hdpos] at h1
    rw [div_lt_iff₀ hdpos] at h2
    have e : Int.fract (c + j * δ) = c + j * δ - ((⌊c⌋ - 1 : ℤ) : ℝ) := by
      rw [Int.fract_eq_iff]
      refine ⟨?_, ?_, ⌊c⌋ - 1, by ring⟩ <;> push_cast <;> nlinarith
    refine ⟨j, ?_⟩
    rw [e]; push_cast
    constructor <;> nlinarith
  · have hdd : d = δ := abs_of_pos hpos
    have harg : 0 ≤ (1 + y' - (c - ⌊c⌋)) / d := div_nonneg (by linarith) hdpos.le
    set j := ⌈(1 + y' - (c - ⌊c⌋)) / d⌉₊
    have h1 := Nat.le_ceil ((1 + y' - (c - ⌊c⌋)) / d)
    have h2 := Nat.ceil_lt_add_one harg
    rw [div_le_iff₀ hdpos] at h1
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hdpos] at h2
    have e : Int.fract (c + j * δ) = c + j * δ - ((⌊c⌋ + 1 : ℤ) : ℝ) := by
      rw [Int.fract_eq_iff]
      refine ⟨?_, ?_, ⌊c⌋ + 1, by ring⟩ <;> push_cast <;> nlinarith
    refine ⟨j, ?_⟩
    rw [e]; push_cast
    constructor <;> nlinarith

/-- For irrational `θ` and any integer `N`, the fractional parts `Int.fract (x * θ)` with
`x : ℤ`, `N ≤ x`, are dense in `[0, 1]`. -/
@[mmp "lem_mmp_foundation_irrational_positive_tail_fractional_dense"]
public theorem Irrational.Icc_subset_closure_fract_mul {θ : ℝ} (hθ : Irrational θ) (N : ℤ) :
    Set.Icc (0 : ℝ) 1 ⊆ closure ((fun x : ℤ => Int.fract ((x : ℝ) * θ)) '' Set.Ici N) := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hε (by norm_num : (0 : ℝ) < 1))
  obtain ⟨p, q, hq0, -, hpq⟩ := Real.exists_int_int_abs_mul_sub_le θ n.succ_pos
  set δ := (q : ℝ) * θ - p with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr ((hθ.intCast_mul hq0.ne').ne_int p)
  have hsmall : |δ| < min ε 1 := hpq.trans_lt (lt_of_le_of_lt (by gcongr; simp) hn)
  obtain ⟨j, hj⟩ := exists_nat_abs_fract_add_mul_sub_le ((N : ℝ) * θ) δ y hδ0
    (hsmall.trans_le (min_le_right _ _)) hy
  refine ⟨_, ⟨N + j * q, by simp only [Set.mem_Ici]; nlinarith, rfl⟩, ?_⟩
  have e : ((N + j * q : ℤ) : ℝ) * θ = (N : ℝ) * θ + j * δ + ((j * p : ℤ) : ℝ) := by
    rw [hδ]; push_cast; ring
  dsimp only
  rw [e, Int.fract_add_intCast, Real.dist_eq, abs_sub_comm]
  exact hj.trans_lt (hsmall.trans_le (min_le_left _ _))

end MMP.Foundation

/-! ### Relative Serre generation over an affine base -/

section RelativeSerre

namespace MMP.Mori

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Stacks.Ample

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

/-- **Relative Serre generation over an affine base.** If `g : Z ⟶ Y` is a projective morphism of
varieties over `k` with `Y` affine, `L` is a `g`-ample invertible sheaf on `Z` and `𝓕` is a
coherent sheaf on `Z`, then `𝓕 ⊗ L^{⊗ m}` is globally generated for all sufficiently large
`m`. -/
@[mmp "lem_mmp_foundation_km3c_relative_serre_generation"]
public theorem isGeneratedByGlobalSections_tensor_tensorPowModule_of_isRelativelyAmple
    {k : Type u} [Field k] {Z Y : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hZ : IsVariety k sZ) (hY : IsVariety k sY) (g : Z ⟶ Y) (hg : g ≫ sY = sZ)
    (hgp : AlgebraicGeometry.IsProjective g) [IsAffine Y]
    (L : Z.Modules) [IsInvertibleModule Z L] (hL : IsRelativelyAmple g L)
    (𝓕 : Z.Modules) [Stacks.SheafOfModules.IsCoherent 𝓕] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      SheafOfModules.IsGeneratedByGlobalSections.{u, u, u}
        (𝓕 ⊗ tensorPowModule Z L m : Z.Modules) := by
  have := hZ.toQuasiCompact
  have : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  have hamp : IsAmple Z L := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple g L).mp
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple g L
      ((quasiCompact_iff_compactSpace g).mpr inferInstance) hL)
  have hcoh : SheafOfModules.IsCoherent 𝓕 :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent inferInstance
  exact (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
    L hamp).2 𝓕 (isQuasicoherent_of_isCoherent 𝓕) hcoh.isFiniteType

end MMP.Mori

end RelativeSerre

/-! ### Proper morphisms with a relatively ample sheaf or divisor are projective -/

namespace MMP

open AlgebraicGeometry CategoryTheory

/-- A proper morphism `f : X ⟶ S` to a Noetherian scheme admitting an `f`-ample invertible sheaf
`L` is projective. -/
@[mmp "lem_mmp_foundation_proper_relative_ample_module_projective"]
public theorem isProjective_of_isProper_of_isRelativelyAmple {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Mori.IsRelativelyAmple f L) : IsProjective f := by
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f L :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L
      inferInstance hL
  have : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace S := IsNoetherian.toCompactSpace
  have : QuasiSeparatedSpace S := IsLocallyNoetherian.quasiSeparatedSpace
  exact (isProjective_iff_isQuasiProjective_and_isProper f).mpr
    ⟨⟨⟨inferInstance, inferInstance⟩, L, inferInstance, hrel⟩, inferInstance⟩

/-- A proper morphism `f : X ⟶ Y` of varieties over a field `k`, with `X` normal, admitting an
`f`-ample Cartier divisor `L` is projective. -/
@[mmp "lem_mmp_foundation_km_proper_relatively_ample_projective"]
public theorem isProjective_of_isProper_of_divisor_isRelativelyAmple (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX]
    [IsVariety k sY] [IsNormal X] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    ∀ (L : Mori.Divisor X) (hL : L.IsCartier), L.IsRelativelyAmple f hL → IsProjective f := by
  intro L hL h
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsNoetherian Y := {}
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact isProjective_of_isProper_of_isRelativelyAmple f _ h

end MMP
