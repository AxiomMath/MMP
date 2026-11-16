module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsCocycle
public import StacksFrontier.AlgebraicGeometry.FlatPullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US

/-!
# Injective and surjective morphisms of modules over a generic stage

Let `K` be a field, `k₀ ⟶ K` a Noetherian coefficient ring, and `Y` a scheme of finite type over
a finitely generated `k₀`-subalgebra `R ⊆ K`. A coherent module on `Y` whose pullback to the
generic fibre `Y_K` vanishes has support a closed subset of `Y` missing the generic fibre, hence
lying over the zero locus of a single nonzero element `s ∈ R`; so it vanishes after base change
to every stage on which `s` is invertible, such as `R[1/s] ⊆ K`.

Applied to the kernel and the cokernel of a morphism of modules of finite presentation, this
shows that a morphism whose base change to `K` is injective, resp. surjective, is injective,
resp. surjective, over `R[1/s]`. The flatness of `R ⟶ K` and of `R ⟶ R[1/s]` makes the base
changes of the kernel the kernels of the base changes.

## Main results

* `MMP.CoefficientModels.exists_ne_zero_mem_of_isClosed`: a closed subset of a Noetherian sober
  space mapping to `Spec R` and missing the generic fibre lies over `V(s)` for some `s ≠ 0`.
* `MMP.CoefficientModels.exists_fgSub_away`: inverting a nonzero element of a finitely generated
  subalgebra `R ⊆ K` gives a finitely generated subalgebra, flat over `R`.
* `MMP.CoefficientModels.DiagramStageData.exists_isZero_pullback_stageMap`: a coherent module on
  a stage whose pullback to the limit vanishes vanishes at every stage inverting some `s ≠ 0`.
* `MMP.CoefficientModels.DiagramStageData.exists_mono_pullback_stageMap` and
  `MMP.CoefficientModels.DiagramStageData.exists_epi_pullback_stageMap`: injectivity and
  surjectivity at the limit hold at every flat stage inverting some `s ≠ 0`.
* `MMP.CoefficientModels.MapStageData.exists_mono_epi`: for the models of a finite system of
  morphisms of modules, a single later stage at which the model morphisms of the injective and
  of the surjective morphisms are injective and surjective.

## References

* [EGA IV₃, §8]
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace MMP.CoefficientModels

/-! ### Algebra and topology over a domain -/

/-- **A closed subset of a Noetherian sober space over `Spec R` missing the generic fibre lies
over `V(s)` for a nonzero `s`.** The closed subset is a finite union of irreducible closed
subsets, each the closure of its generic point; the image of a generic point is a nonzero prime,
which contains a nonzero element, and the images of the points of its closure are larger primes.
-/
theorem exists_ne_zero_mem_of_isClosed {R : Type*} [CommRing R] [IsDomain R] {Y : Type*}
    [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y]
    (f : Y → PrimeSpectrum R) (hf : Continuous f) {Z : Set Y} (hZ : IsClosed Z)
    (h : ∀ y ∈ Z, (f y).asIdeal ≠ ⊥) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ Z, s ∈ (f y).asIdeal := by
  classical
  obtain ⟨S, hS, hSc, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have key : ∀ t ∈ S, ∃ s : R, s ≠ 0 ∧ ∀ y ∈ t, s ∈ (f y).asIdeal := by
    intro t ht
    obtain ⟨g, hg⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h g ⟨t, ht, hg.mem⟩)
    exact ⟨s, hs0, fun y hy =>
      (PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hy).map hf) hs⟩
  choose! s hs0 hs using key
  refine ⟨∏ t ∈ hS.toFinset, s t, Finset.prod_ne_zero_iff.mpr fun t ht => hs0 t
    (hS.mem_toFinset.mp ht), fun y hy => ?_⟩
  obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.mp hy
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (hS.mem_toFinset.mpr ht)) (hs t ht y hyt)

/-- A field is flat over each of its subalgebras: it is a vector space over the fraction field of
the subalgebra, which is a localization. -/
theorem flat_subalgebra_field {k₀ K : Type*} [CommRing k₀] [Field K] [Algebra k₀ K]
    (R : Subalgebra k₀ K) : Module.Flat R K := by
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := Subtype.val_injective
  let _ : Algebra F K := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower R F K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  have : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have : Module.Free F K := Module.Free.of_divisionRing F K
  have : Module.Flat F K := Module.Flat.of_free
  exact Module.Flat.trans R F K

/-- **Inverting a nonzero element of a finitely generated subalgebra of a field.** For `s ≠ 0`
in a finitely generated `k₀`-subalgebra `R ⊆ K`, the subalgebra `R[1/s] ⊆ K` is finitely
generated, `s` is a unit in it, and it is flat over `R`, being the localization `R_s`. -/
theorem exists_fgSub_away {k₀ K : Type*} [CommRing k₀] [Field K] [Algebra k₀ K]
    (R : FGSub k₀ K) (s : R.1) (hs : s ≠ 0) :
    ∃ (R' : FGSub k₀ K) (h : R ≤ R'), IsUnit (Subalgebra.inclusion h s) ∧
      (Subalgebra.inclusion h).toRingHom.Flat := by
  classical
  obtain ⟨t, ht⟩ := R.2
  let R' := Algebra.adjoin k₀ ((insert (s : K)⁻¹ t : Finset K) : Set K)
  have h : R.1 ≤ R' := by
    rw [← ht]
    exact Algebra.adjoin_mono (by simp)
  have hs' : (s : K) ≠ 0 := fun h0 => hs (Subtype.ext h0)
  have hinv : (s : K)⁻¹ ∈ R' := Algebra.subset_adjoin (by simp)
  have hunit : IsUnit (Subalgebra.inclusion h s) :=
    IsUnit.of_mul_eq_one (b := ⟨(s : K)⁻¹, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hs'))
  refine ⟨⟨R', Subalgebra.fg_adjoin_finset _⟩, h, hunit, ?_⟩
  let _ : Algebra R.1 R' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have hloc : IsLocalization.Away s R' := by
    refine IsLocalization.Away.mk s hunit (fun z => ?_) (fun a b hab => ⟨0, ?_⟩)
    · obtain ⟨z, hz⟩ := z
      have key : ∃ (n : ℕ) (a : K), a ∈ R.1 ∧ z * (s : K) ^ n = a := by
        induction hz using Algebra.adjoin_induction with
        | mem x hx =>
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ⟨1, 1, one_mem _, by rw [pow_one, inv_mul_cancel₀ hs']⟩
          · exact ⟨0, x, ht ▸ Algebra.subset_adjoin hx, by simp⟩
        | algebraMap r => exact ⟨0, algebraMap k₀ K r, R.1.algebraMap_mem r, by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨n, a, ha, hxa⟩ := hx
          obtain ⟨m, b, hb, hyb⟩ := hy
          refine ⟨n + m, a * (s : K) ^ m + b * (s : K) ^ n,
            add_mem (mul_mem ha (pow_mem s.2 _)) (mul_mem hb (pow_mem s.2 _)), ?_⟩
          rw [← hxa, ← hyb]
          ring
        | mul x y _ _ hx hy =>
          obtain ⟨n, a, ha, hxa⟩ := hx
          obtain ⟨m, b, hb, hyb⟩ := hy
          exact ⟨n + m, a * b, mul_mem ha hb, by rw [← hxa, ← hyb]; ring⟩
      obtain ⟨n, a, ha, hza⟩ := key
      exact ⟨n, ⟨a, ha⟩, Subtype.ext hza⟩
    · obtain rfl : a = b := Subtype.ext (congrArg (Subtype.val : R' → K) hab)
      rfl
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat R' (Submonoid.powers s))

/-! ### Kernels and cokernels under pullback -/

section Exact

variable {S T : Scheme.{u}} (g : S ⟶ T) {A B : T.Modules} (Ψ : A ⟶ B)

/-- Along a flat morphism, a morphism with injective pullback has a kernel with zero pullback. -/
theorem isZero_pullback_kernel_of_mono [Flat g] (h : Mono ((Scheme.Modules.pullback g).map Ψ)) :
    IsZero ((Scheme.Modules.pullback g).obj (kernel Ψ)) := by
  have := preservesFiniteLimits_pullback_of_flat g
  have h0 : (Scheme.Modules.pullback g).map (kernel.ι Ψ) = 0 := by
    rw [← cancel_mono ((Scheme.Modules.pullback g).map Ψ), ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp]
  have hm : Mono ((Scheme.Modules.pullback g).map (kernel.ι Ψ)) := inferInstance
  rw [h0] at hm
  exact @IsZero.of_mono_zero _ _ _ _ _ hm

/-- Along a flat morphism, a morphism whose kernel has zero pullback has injective pullback. -/
theorem mono_pullback_map_of_isZero [Flat g]
    (h : IsZero ((Scheme.Modules.pullback g).obj (kernel Ψ))) :
    Mono ((Scheme.Modules.pullback g).map Ψ) := by
  have := preservesFiniteLimits_pullback_of_flat g
  exact Preadditive.mono_of_isZero_kernel' _
    (KernelFork.mapIsLimit _ (kernelIsKernel Ψ) (Scheme.Modules.pullback g)) h

/-- A morphism with surjective pullback has a cokernel with zero pullback. -/
theorem isZero_pullback_cokernel_of_epi (h : Epi ((Scheme.Modules.pullback g).map Ψ)) :
    IsZero ((Scheme.Modules.pullback g).obj (cokernel Ψ)) := by
  have h0 : (Scheme.Modules.pullback g).map (cokernel.π Ψ) = 0 := by
    rw [← cancel_epi ((Scheme.Modules.pullback g).map Ψ), ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero]
  have he : Epi ((Scheme.Modules.pullback g).map (cokernel.π Ψ)) := inferInstance
  rw [h0] at he
  exact @IsZero.of_epi_zero _ _ _ _ _ he

/-- A morphism whose cokernel has zero pullback has surjective pullback. -/
theorem epi_pullback_map_of_isZero (h : IsZero ((Scheme.Modules.pullback g).obj (cokernel Ψ))) :
    Epi ((Scheme.Modules.pullback g).map Ψ) :=
  Preadditive.epi_of_isZero_cokernel' _
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel Ψ) (Scheme.Modules.pullback g)) h

end Exact

/-! ### Vanishing over a generic stage -/

section Stage

variable {k₀ : Type v} [CommRing k₀] {K : Type u} [Field K] [Algebra k₀ K] {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over (specCone k₀ K).pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n (specCone k₀ K).pt}
  (d : DiagramStageData (specDiagram k₀ K) (specCone k₀ K) n X ι)

namespace DiagramStageData

/-- The projections from the given diagram to its models are flat, as base changes of the flat
morphism `Spec K ⟶ Spec R`. -/
theorem flat_proj (b : Over d.i₀) (j : J) : Flat (d.proj b j) := by
  have : Flat ((specCone k₀ K).π.app b.left) := by
    rw [specCone_π_app]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (algebraMap b.left.unop.1 K))).mpr
        (RingHom.flat_algebraMap_iff.mpr (flat_subalgebra_field b.left.unop.1))
  exact MorphismProperty.of_isPullback (d.isPullback_proj b j).flip this

/-- A transition morphism of stages over a flat ring map is flat. -/
theorem flat_stageMap (j : J) {m b : Over d.i₀} (e : m ⟶ b)
    (h : (Subalgebra.inclusion (leOfHom e.left.unop)).toRingHom.Flat) :
    Flat (stageMap (specDiagram k₀ K) (d.W j) e) :=
  MorphismProperty.of_isPullback (isPullback_stageMap _ _ e).flip
    ((HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom e.left.unop)).toRingHom)).mpr h)

/-- **A coherent module on a stage whose pullback to the limit vanishes vanishes at every stage
inverting some nonzero element.** Its support is closed and misses the generic fibre, which is
the image of the flat projection from the limit, so it lies over `V(s)` for some `s ≠ 0`. -/
theorem exists_isZero_pullback_stageMap [IsNoetherianRing k₀] (j : J) (b : Over d.i₀)
    (F : (stageObj (specDiagram k₀ K) (d.W j) b).Modules) (hF : F.IsCoherent)
    (h0 : IsZero ((Scheme.Modules.pullback (d.proj b j)).obj F)) :
    ∃ s : b.left.unop.1, s ≠ 0 ∧ ∀ {m : Over d.i₀} (e : m ⟶ b),
      IsUnit (Subalgebra.inclusion (leOfHom e.left.unop) s) →
      IsZero ((Scheme.Modules.pullback (stageMap (specDiagram k₀ K) (d.W j) e)).obj F) := by
  have : LocallyOfFinitePresentation (d.W j).hom := (d.finitePresentation j).1
  have : IsLocallyNoetherian (stageObj (specDiagram k₀ K) (d.W j) b) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom)
  have : CompactSpace (stageObj (specDiagram k₀ K) (d.W j) b) :=
    compactSpace_stageObj _ (d.W j) (d.finitePresentation j) b
  have : IsNoetherian (stageObj (specDiagram k₀ K) (d.W j) b) := ⟨⟩
  have := d.flat_proj b j
  have hZ := Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent F hF
  have hgen : ∀ y ∈ SheafOfModules.supp F, (show PrimeSpectrum b.left.unop.1 from
      pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom y).asIdeal ≠ ⊥ := by
    intro y hy hbot
    let pt : (specCone k₀ K).pt := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hpt : pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom y =
        (specCone k₀ K).π.app b.left pt :=
      PrimeSpectrum.ext <| hbot.trans (Ideal.comap_bot_of_injective _ Subtype.val_injective).symm
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y pt hpt
    have hpb := d.isPullback_proj b j
    have hz : d.proj b j (hpb.isoPullback.inv w) = y := by
      rwa [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
    have hs := Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_stalk_of_isZero_pullback
      (d.proj b j) F (hpb.isoPullback.inv w) h0
    rw [hz] at hs
    exact not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp hs)
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk F y).mp hy)
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_mem_of_isClosed
    (fun y => (show PrimeSpectrum b.left.unop.1 from
      pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom y))
    (pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom).continuous hZ hgen
  refine ⟨s, hs0, fun {m} e hunit => ?_⟩
  refine Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_pullback_of_forall_isZero_stalk _ F
    fun z => ?_
  by_contra hne
  have hmem : stageMap (specDiagram k₀ K) (d.W j) e z ∈ SheafOfModules.supp F := by
    refine (SheafOfModules.mem_supp_iff_nontrivial_stalk F _).mpr ?_
    refine not_subsingleton_iff_nontrivial.mp fun hsub => hne ?_
    exact @AddCommGrpCat.isZero_of_subsingleton _ hsub
  have hfz : pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom
      (stageMap (specDiagram k₀ K) (d.W j) e z) = (specDiagram k₀ K).map e.left
        (pullback.fst ((specDiagram k₀ K).map m.hom) (d.W j).hom z) := by
    rw [← Scheme.Hom.comp_apply, stageMap_fst, Scheme.Hom.comp_apply]
  have hsz := hs _ hmem
  simp only [hfz] at hsz
  exact (show PrimeSpectrum m.left.unop.1 from
    pullback.fst ((specDiagram k₀ K).map m.hom) (d.W j).hom z).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hsz hunit)

/-- **Injectivity at the limit holds at every flat stage inverting some nonzero element.** -/
theorem exists_mono_pullback_stageMap [IsNoetherianRing k₀] (j : J) (b : Over d.i₀)
    {A B : (stageObj (specDiagram k₀ K) (d.W j) b).Modules} (hA : A.IsFinitePresentation)
    (hB : B.IsFinitePresentation) (Ψ : A ⟶ B)
    (h : Mono ((Scheme.Modules.pullback (d.proj b j)).map Ψ)) :
    ∃ s : b.left.unop.1, s ≠ 0 ∧ ∀ {m : Over d.i₀} (e : m ⟶ b),
      IsUnit (Subalgebra.inclusion (leOfHom e.left.unop) s) →
      (Subalgebra.inclusion (leOfHom e.left.unop)).toRingHom.Flat →
      Mono ((Scheme.Modules.pullback (stageMap (specDiagram k₀ K) (d.W j) e)).map Ψ) := by
  have : LocallyOfFinitePresentation (d.W j).hom := (d.finitePresentation j).1
  have : IsLocallyNoetherian (stageObj (specDiagram k₀ K) (d.W j) b) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom)
  have := d.flat_proj b j
  have hK := Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation A hA)
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation B hB) Ψ
  obtain ⟨s, hs0, hs⟩ := d.exists_isZero_pullback_stageMap j b (kernel Ψ) hK
    (isZero_pullback_kernel_of_mono _ Ψ h)
  refine ⟨s, hs0, fun {m} e hu hfl => ?_⟩
  have := d.flat_stageMap j e hfl
  exact mono_pullback_map_of_isZero _ Ψ (hs e hu)

/-- **Surjectivity at the limit holds at every stage inverting some nonzero element.** -/
theorem exists_epi_pullback_stageMap [IsNoetherianRing k₀] (j : J) (b : Over d.i₀)
    {A B : (stageObj (specDiagram k₀ K) (d.W j) b).Modules} (hA : A.IsFinitePresentation)
    (hB : B.IsFinitePresentation) (Ψ : A ⟶ B)
    (h : Epi ((Scheme.Modules.pullback (d.proj b j)).map Ψ)) :
    ∃ s : b.left.unop.1, s ≠ 0 ∧ ∀ {m : Over d.i₀} (e : m ⟶ b),
      IsUnit (Subalgebra.inclusion (leOfHom e.left.unop) s) →
      Epi ((Scheme.Modules.pullback (stageMap (specDiagram k₀ K) (d.W j) e)).map Ψ) := by
  have : LocallyOfFinitePresentation (d.W j).hom := (d.finitePresentation j).1
  have : IsLocallyNoetherian (stageObj (specDiagram k₀ K) (d.W j) b) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst ((specDiagram k₀ K).map b.hom) (d.W j).hom)
  have hQ := Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation A hA)
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation B hB) Ψ
  obtain ⟨s, hs0, hs⟩ := d.exists_isZero_pullback_stageMap j b (cokernel Ψ) hQ
    (isZero_pullback_cokernel_of_epi _ Ψ h)
  exact ⟨s, hs0, fun {m} e hu => epi_pullback_map_of_isZero _ Ψ (hs e hu)⟩

end DiagramStageData

end Stage

/-! ### Injective and surjective models of morphisms -/

section Transport

variable {V W T₁ T₂ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules} (r : V ⟶ W)
  {s₁ : W ⟶ T₁} {s₂ : W ⟶ T₂} {t₁ : V ⟶ T₁} {t₂ : V ⟶ T₂} (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂)
  (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B)

/-- The transport `transport r h₁ h₂ Ψ` is a monomorphism if and only if the pullback of `Ψ`
along `r` is. -/
theorem mono_transport_iff :
    Mono (transport r h₁ h₂ Ψ) ↔ Mono ((Scheme.Modules.pullback r).map Ψ) := by
  rw [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, mono_comp_iff_of_isIso,
    mono_comp_iff_of_mono]

/-- The transport `transport r h₁ h₂ Ψ` is an epimorphism if and only if the pullback of `Ψ`
along `r` is. -/
theorem epi_transport_iff :
    Epi (transport r h₁ h₂ Ψ) ↔ Epi ((Scheme.Modules.pullback r).map Ψ) := by
  rw [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, epi_comp_iff_of_epi,
    epi_comp_iff_of_isIso]

end Transport

section MapStageData

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} {d : DiagramStageData D c n X ι}
  {E : Type*} [Category E] {π : E ⥤ J} {M : ∀ e, (X.obj (π.obj e)).left.Modules}
  {md : ModuleStageData d π M}
  {μ : ∀ {e e' : E} (φ : e ⟶ e'),
    M e ⟶ (Scheme.Modules.pullback (X.map (π.map φ)).left).obj (M e')}

namespace MapStageData

variable (ms : MapStageData md μ)

/-- The model of `μ φ` at a later stage is the transport of the model at an earlier stage. -/
theorem stageHom_comp {m b : Over d.i₀} (bm : m ⟶ b) (bb : b ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    ms.stageHom (bm ≫ bb) φ = transport (stageMap D (d.W (π.obj e)) bm)
      (by rw [← stageMap_comp]; simp only [Category.assoc])
      (by
        rw [← Category.assoc, ← stageLift_stageMap (d.H (π.map φ)) (d.H_w _) bm
            (((bb ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ((((bm ≫ bb) ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)
            (by simp only [Category.assoc]), Category.assoc, ← stageMap_comp]
        simp only [Category.assoc])
      (ms.stageHom bb φ) := by
  rw [stageHom_def, stageHom_def, transport_transport]
  · exact transport_congr (stageMap_comp D _ bm bb) _ _ _ _ _
  · rw [← stageMap_comp, ← stageMap_comp]
    simp only [Category.assoc]
  · rw [← stageMap_comp]
    exact ms.stageMap_stageLift_stageMap_bₑ (bm ≫ bb) φ

end MapStageData

end MapStageData

section MonoEpi

variable {k₀ : Type v} [CommRing k₀] {K : Type u} [Field K] [Algebra k₀ K] {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over (specCone k₀ K).pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n (specCone k₀ K).pt}
  {d : DiagramStageData (specDiagram k₀ K) (specCone k₀ K) n X ι}
  {E : Type*} [Category E] {π : E ⥤ J} {M : ∀ e, (X.obj (π.obj e)).left.Modules}
  {md : ModuleStageData d π M}
  {μ : ∀ {e e' : E} (φ : e ⟶ e'),
    M e ⟶ (Scheme.Modules.pullback (X.map (π.map φ)).left).obj (M e')}

namespace MapStageData

variable (ms : MapStageData md μ)

/-- **For one arrow there is a nonzero element inverting which makes the pulled-back stage
morphism injective, resp. surjective, whenever `μ φ` is**: the product of the elements given by
`exists_mono_pullback_stageMap` and `exists_epi_pullback_stageMap`. -/
theorem exists_mono_epi_pullback_stageHom [IsNoetherianRing k₀] {b : Over d.i₀} (bb : b ⟶ ms.a)
    {e e' : E} (φ : e ⟶ e') :
    ∃ s : b.left.unop.1, s ≠ 0 ∧
      ∀ {m : Over d.i₀} (y : m ⟶ b), IsUnit (Subalgebra.inclusion (leOfHom y.left.unop) s) →
        (Subalgebra.inclusion (leOfHom y.left.unop)).toRingHom.Flat →
        (Mono (μ φ) → Mono ((Scheme.Modules.pullback
          (stageMap (specDiagram k₀ K) (d.W (π.obj e)) y)).map (ms.stageHom bb φ))) ∧
        (Epi (μ φ) → Epi ((Scheme.Modules.pullback
          (stageMap (specDiagram k₀ K) (d.W (π.obj e)) y)).map (ms.stageHom bb φ))) := by
  have := md.isFinitePresentation e
  have := md.isFinitePresentation e'
  have hA := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageMap (specDiagram k₀ K) (d.W (π.obj e)) ((bb ≫ ms.ba) ≫ md.bₑ e)) (md.N₀ e)
  have hB := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageLift (d.H (π.map φ)) (d.H_w _) (((bb ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
      stageMap (specDiagram k₀ K) (d.W (π.obj e')) ((bb ≫ ms.ba) ≫ md.bₑ e')) (md.N₀ e')
  have hlim := ms.transport_proj_stageHom bb φ
  obtain ⟨s₁, h₁0, h₁⟩ : ∃ s : b.left.unop.1, s ≠ 0 ∧
      ∀ {m : Over d.i₀} (y : m ⟶ b), IsUnit (Subalgebra.inclusion (leOfHom y.left.unop) s) →
        (Subalgebra.inclusion (leOfHom y.left.unop)).toRingHom.Flat →
        Mono (μ φ) → Mono ((Scheme.Modules.pullback
          (stageMap (specDiagram k₀ K) (d.W (π.obj e)) y)).map (ms.stageHom bb φ)) := by
    by_cases hm : Mono (μ φ)
    · have hl : Mono (md.limitMap μ φ) := by
        rw [ModuleStageData.limitMap]
        exact mono_comp' (IsIso.mono_of_iso _)
          (mono_comp' hm (mono_comp' (IsIso.mono_of_iso _) (IsIso.mono_of_iso _)))
      rw [← hlim, mono_transport_iff] at hl
      obtain ⟨s, hs0, hs⟩ := d.exists_mono_pullback_stageMap (π.obj e) b hA hB _ hl
      exact ⟨s, hs0, fun y hu hf _ => hs y hu hf⟩
    · exact ⟨1, one_ne_zero, fun _ _ _ h => absurd h hm⟩
  obtain ⟨s₂, h₂0, h₂⟩ : ∃ s : b.left.unop.1, s ≠ 0 ∧
      ∀ {m : Over d.i₀} (y : m ⟶ b), IsUnit (Subalgebra.inclusion (leOfHom y.left.unop) s) →
        Epi (μ φ) → Epi ((Scheme.Modules.pullback
          (stageMap (specDiagram k₀ K) (d.W (π.obj e)) y)).map (ms.stageHom bb φ)) := by
    by_cases hm : Epi (μ φ)
    · have hl : Epi (md.limitMap μ φ) := by
        rw [ModuleStageData.limitMap]
        exact epi_comp' (IsIso.epi_of_iso _)
          (epi_comp' hm (epi_comp' (IsIso.epi_of_iso _) (IsIso.epi_of_iso _)))
      rw [← hlim, epi_transport_iff] at hl
      obtain ⟨s, hs0, hs⟩ := d.exists_epi_pullback_stageMap (π.obj e) b hA hB _ hl
      exact ⟨s, hs0, fun y hu _ => hs y hu⟩
    · exact ⟨1, one_ne_zero, fun _ _ h => absurd h hm⟩
  refine ⟨s₁ * s₂, mul_ne_zero h₁0 h₂0, fun {m} y hu hf => ?_⟩
  rw [map_mul] at hu
  exact ⟨h₁ y (isUnit_of_mul_isUnit_left hu) hf, h₂ y (isUnit_of_mul_isUnit_right hu)⟩

/-- **Below any stage there is a stage at which the model morphisms of the injective and of the
surjective morphisms `μ φ` are injective and surjective**: the stage `R[1/s]` for a product `s`
of the nonzero elements given by `exists_mono_pullback_stageMap` and
`exists_epi_pullback_stageMap`, one for each of the finitely many arrows. -/
theorem exists_mono_epi [IsNoetherianRing k₀] [FinCategory E] {b : Over d.i₀} (bb : b ⟶ ms.a) :
    ∃ (m : Over d.i₀) (bm : m ⟶ b), ∀ {e e' : E} (φ : e ⟶ e'),
      (Mono (μ φ) → Mono (ms.modelHom (bm ≫ bb) φ)) ∧
        (Epi (μ φ) → Epi (ms.modelHom (bm ≫ bb) φ)) := by
  classical
  choose s hs0 hs using fun (e e' : E) (φ : e ⟶ e') => ms.exists_mono_epi_pullback_stageHom bb φ
  let t : b.left.unop.1 := ∏ x : (Σ (e : E) (e' : E), e ⟶ e'), s x.1 x.2.1 x.2.2
  have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => hs0 _ _ _
  obtain ⟨R', h, hu, hfl⟩ := exists_fgSub_away b.left.unop t ht0
  let m : Over d.i₀ := Over.mk ((homOfLE h).op ≫ b.hom)
  let bm : m ⟶ b := Over.homMk (homOfLE h).op
  refine ⟨m, bm, fun {e e'} φ => ?_⟩
  have hu' : IsUnit (Subalgebra.inclusion (leOfHom bm.left.unop) (s e e' φ)) :=
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem
      (fun x : (Σ (e : E) (e' : E), e ⟶ e') => s x.1 x.2.1 x.2.2)
      (Finset.mem_univ (⟨e, e', φ⟩ : Σ (e : E) (e' : E), e ⟶ e')))) hu
  obtain ⟨hmo, hep⟩ := hs e e' φ bm hu' hfl
  rw [modelHom_def, ms.stageHom_comp bm bb φ]
  refine ⟨fun hμ => ?_, fun hμ => ?_⟩
  · refine @mono_comp _ _ _ _ _ _ ?_ _ (Iso.isIso_inv _).mono_of_iso
    exact (mono_transport_iff _ _ _ _).mpr (hmo hμ)
  · refine @epi_comp _ _ _ _ _ _ ?_ _ (Iso.isIso_inv _).epi_of_iso
    exact (epi_transport_iff _ _ _ _).mpr (hep hμ)

end MapStageData

end MonoEpi

end MMP.CoefficientModels

end
