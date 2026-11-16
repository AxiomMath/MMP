module

public import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
public import MMP.AlgebraicGeometry.Divisor.QuasiProjectiveCartierSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase

/-!
# Effective divisors from sections of ample sheaves

## Main results

* `MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple`: on an integral scheme
  with an ample invertible sheaf `L`, a closed set `T` and a point `y₀ ∉ T`, the zero scheme of a
  section of some `L^n` is an effective Cartier divisor containing `T` and avoiding `y₀`, with
  invertible sheaf `L^n`.
* `MMP.Threefold.Resolution.eq_genericPoint_of_map_eq`: the generic fibre of a generically finite
  morphism from an integral scheme is the generic point.
* `MMP.Threefold.Resolution.isRelativelyAmple_add_of_isLocalEquation_preimage`: twisting an
  `f`-ample divisor by a divisor principal over an open cover of the base keeps it `f`-ample.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite RingedSpaceModuleAdjunction MMP.Mori Stacks.Ample

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold.Resolution

variable {Y : Scheme.{u}}

/-- **The zero scheme of a section of a power of an ample sheaf.** On an integral scheme `Y` with
an ample invertible sheaf `L`, for a closed `T` and `y₀ ∉ T` there are `n ≥ 1` and an effective
Cartier divisor `I` with `T ⊆ Supp I`, `y₀ ∉ Supp I` and `L^n ≅ 𝒪_Y(I)`. -/
theorem exists_isEffectiveCartierDivisor_of_isAmple [IsIntegral Y] (L : Y.Modules)
    [IsInvertibleModule Y L] (hL : IsAmple Y L) {T : Set Y} (hT : IsClosed T) {y₀ : Y}
    (hy₀ : y₀ ∉ T) :
    ∃ I : Y.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      T ⊆ I.support ∧ y₀ ∉ I.support ∧ ∃ n : ℕ, 1 ≤ n ∧
        Nonempty (tensorPowModule Y L (n : ℤ) ≅
          (Stacks.Divisors.invertibleSheaf' I : Y.Modules)) := by
  obtain ⟨n, hn, s, -, hηs, hsT⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (Set.finite_singleton y₀) ⟨Tᶜ, hT.isOpen_compl⟩
      (Set.singleton_subset_iff.2 hy₀)
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (tensorPowModule Y L (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : y₀ ∈ nonvanishingLocus (tensorPowModule Y L (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s) ▸ hηs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop
      (tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop
      (tensorPowModule Y L (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (tensorPowModule Y L (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme Y (tensorPowModule Y L (n : ℤ))
        ((Stacks.SheafOfModules.sectionsOfTop
          (tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y _ _).2 hreg
  have hnv : nonvanishingLocus (tensorPowModule Y L (n : ℤ)) s =
      (zeroScheme Y (tensorPowModule Y L (n : ℤ))
        ((Stacks.SheafOfModules.sectionsOfTop
          (tensorPowModule Y L (n : ℤ)) s).eval (op ⊤))).supportSetᶜ := by
    rw [← nonvanishingLocus_eq_compl_supportSet_zeroScheme (tensorPowModule Y L (n : ℤ)) _ hne0']
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Y _
        (Stacks.SheafOfModules.sectionsOfTop (tensorPowModule Y L (n : ℤ)) s)]
    rfl
  refine ⟨_, hZc, ?_, ?_, n, hn,
    ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg⟩⟩
  · intro x hx
    by_contra hxZ
    have hx' : x ∈ nonvanishingLocus (tensorPowModule Y L (n : ℤ)) s := by
      rwa [hnv]
    rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen Y L n s] at hx'
    exact hsT hx' hx
  · intro hy'
    rw [hnv] at hx₀
    exact hx₀ hy'

/-- **No point of the generic fibre of a generically finite morphism other than the generic
point.** If `X` is integral and `f : X ⟶ Y` is finite over an open `V` meeting `f(X)`, every point
`x` with `f(x) = f(η_X)` is `η_X`: the fibre of the finite morphism `f⁻¹(V) ⟶ V` is discrete, and
`η_X` specializes to `x` inside it. -/
theorem eq_genericPoint_of_map_eq {X Y : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y}
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V))
    {x : X} (hx : f x = f (genericPoint X)) : x = genericPoint X := by
  obtain ⟨V, ⟨_, hyV, x', rfl⟩, hfin⟩ := hgf
  have hη : genericPoint X ∈ f ⁻¹ᵁ V :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ V).isOpen).2 ⟨x', trivial, hyV⟩
  have hxV : x ∈ f ⁻¹ᵁ V := by
    change f x ∈ V
    rwa [hx]
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨genericPoint X, hη⟩
  have hpq : (f ∣_ V) q = (f ∣_ V) p := Subtype.ext <| by
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact hx.symm
  have hspec : q ⤳ p := by
    rw [← (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff]
    exact (genericPoint_spec X).specializes (Set.mem_univ _)
  have := (Scheme.Hom.isDiscrete_preimage_singleton (f ∣_ V) ((f ∣_ V) p)).to_subtype
  have h' : (⟨q, hpq⟩ : ((f ∣_ V) ⁻¹' {(f ∣_ V) p} : Set _)) ⤳ ⟨p, rfl⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
  exact (congrArg Subtype.val (congrArg Subtype.val h'.eq)).symm

section Twist

variable {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y)

/-- The restriction of a module to an open subscheme, in the `modulePullback` spelling, is the
restriction `AlgebraicGeometry.Scheme.Modules.restrict`. -/
def modulePullbackIsoRestrict' {Z : Scheme.{u}} (U : Z.Opens) (F : Z.Modules) :
    (modulePullback U.ι.toLRSHom.toShHom).obj F ≅ F.restrict U.ι :=
  (Adjunction.leftAdjointUniq
      (modulePullbackPushforwardAdjunction U.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).app F ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

/-- **Twisting by a divisor principal over the base preserves relative ampleness.** If `L` is an
`f`-ample Cartier divisor and `B` a Cartier divisor which is principal on `f⁻¹(U)` for the members
`U` of an open cover of `Y`, then `L + B` is `f`-ample. -/
theorem isRelativelyAmple_add_of_isLocalEquation_preimage [QuasiCompact f]
    {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL) {B : Divisor X}
    (hBc : B.IsCartier)
    (hB : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
      B.IsLocalEquation (f ⁻¹ᵁ U) ψ) :
    (L + B).IsRelativelyAmple f (hL.add hBc) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.add hBc).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := hLf y
  obtain ⟨U, hyU, ψ, hψ⟩ := hB y
  obtain ⟨V', hV', hyV', hV'le⟩ :=
    exists_isAffineOpen_mem_and_subset (U := V ⊓ U) (show y ∈ V ⊓ U from ⟨hyV, hyU⟩)
  refine ⟨V', hV', hyV', ?_⟩
  have : CompactSpace (f ⁻¹ᵁ V).toScheme := hamp.1
  have hLV' : IsAmple (f ⁻¹ᵁ V').toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V').ι L.divisorialSheaf) :=
    Stacks.RelativeAmpleComposition.isAmple_restrict_of_le
      (f.preimage_mono fun _ hz => (hV'le hz).1) L.divisorialSheaf hamp
      (Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact f V' hV'.isCompact)
  have e : (L + B).divisorialSheaf.restrict (f ⁻¹ᵁ V').ι ≅
      L.divisorialSheaf.restrict (f ⁻¹ᵁ V').ι :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V').ι).mapIso
        (Divisor.divisorialSheafMulIso ψ (D' := L + B - principalDivisor ψ) fun E => by
          rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, sub_add_cancel]) ≪≫
      Divisor.restrictDivisorialSheafIsoOfEqOn fun E hE => by
        rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
          hψ E (hE.mono (Set.inter_subset_inter_right _
            (f.preimage_mono fun _ hz => (hV'le hz).2))),
          add_sub_cancel_right]
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (modulePullbackIsoRestrict' _ _ ≪≫ e ≪≫ (modulePullbackIsoRestrict' _ _).symm)).mpr hLV'

end Twist

end MMP.Threefold.Resolution
