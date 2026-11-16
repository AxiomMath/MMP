module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension

universe u

section

/-!
## Proof: intersection with a moving family of contracted curves

Let `X → V → S` be projective morphisms of projective varieties over an algebraically closed
field `k` of characteristic zero, with `X` normal and `ℚ`-factorial and `f : X → V` a contraction
of fibre type. If `-D` is ample over `V`, then `D` is not pseudo-effective over `S`.

Put `v = dim V` and `n = dim X > v`, and choose ample invertible sheaves `A` on `V` and `H` on `X`.
The intersection number `φ(L) = (f^*A)^v · H^{n-v-1} · L` (Stacks, Tag 0BEP) is computed by
cutting `X` successively with general sections: `v` pull-backs of sections of powers of `A`,
then `n - v - 1` sections of powers of `H`, each chosen not to vanish at the finitely many
associated points of the preceding cut, so that it is an effective Cartier divisor on it
(Stacks, Tags 0AYL and 0BEU). The resulting closed subscheme `Z` has dimension at most one,
lies over finitely many points of `V`, and `φ(L)` is a positive multiple of
`∑ m_W (L · W)` over the one-dimensional components `W` of `Z` (Stacks, Tag 0BES). These
curves are contracted by `f`; there is at least one of them, because the first `v` cuts lie
over a nonempty finite set of points of `V` and every fibre of `f` has dimension at least
`n - v`. Cutting first by an effective Cartier divisor `E` instead shows `φ(𝒪_X(E)) ≥ 0`. Hence
`z ↦ ∑ m_W (z · W)` is a continuous linear form on `N¹(X/S)`, nonnegative on the effective cone
and negative on `D`, since `-D` is a positive combination of `f`-ample Cartier divisors.

## References

* [Stacks Project, Tags 0BEP, 0BES, 0BEU, 0BEV, 0AYL, 09NV]
-/

namespace MMP.FourfoldProofs.FourfoldNegativeFiberNotPseudoeffectiveProof

open AlgebraicGeometry CategoryTheory TensorProduct Opposite

section Cut

variable {Y Z : Scheme.{u}}

/-- **Cutting a closed subscheme by a section.** Let `i : Z ⟶ Y` be a closed immersion with `Z`
locally Noetherian, and `s` a global section of an invertible module `M` on `Y` not vanishing at
the image of any associated point of `Z`. Then `s|_Z` is a regular section, its zero scheme is an
effective Cartier divisor `D ⊆ Z` with `𝒪_Z(D) ≅ M|_Z`, and `D` is the part of `Z` where `s`
vanishes. -/
private theorem exists_cut (i : Z ⟶ Y) [IsClosedImmersion i] [IsLocallyNoetherian Z]
    (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (s : Γ(M, ⊤))
    (hs : ∀ z ∈ Stacks.Divisors.schemeAssociatedPoints Z,
      i z ∈ Stacks.Ample.nonvanishingLocus M s) :
    ∃ Dv : Z.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor Dv ∧
      Nonempty ((Scheme.Modules.pullback i).obj M ≅ Stacks.Divisors.invertibleSheaf Dv) ∧
      Set.range (Dv.subschemeι ≫ i) = Set.range i ∩ (Stacks.Ample.nonvanishingLocus M s)ᶜ := by
  set M' := (Scheme.Modules.pullback i).obj M
  set s' := (pullbackGlobalSections i M).hom s
  have hpre := Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i M s
  have hinv : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M' :=
    isInvertible_pullbackObj i M
  set σ := Stacks.SheafOfModules.sectionsOfTop M' s'
  have hσ : σ.eval (op ⊤) = s' := Stacks.SheafOfModules.sectionsOfTop_eval_top _ s'
  have hreg : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property σ := by
    refine (Stacks.Divisors.isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul
      M' σ).2 fun z hz => ?_
    have h1 : z ∈ i ⁻¹' Stacks.Ample.nonvanishingLocus M s := hs z hz
    rw [hpre] at h1
    rw [hσ]
    exact h1
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme Z M' (σ.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Z M' σ).mpr hreg
  refine ⟨zeroScheme Z M' (σ.eval (op ⊤)), hD,
    ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection M' σ hreg⟩, ?_⟩
  have hsec : _root_.SheafOfModules.sectionsMap
      (invertibleSheafIsoZeroSchemeOfIsRegularSection M' σ hreg).hom σ =
      Stacks.Divisors.canonicalSections (zeroScheme Z M' (σ.eval (op ⊤))) :=
    Scheme.Modules.sections_ext_of_eval_top
      (invertibleSheafIsoZeroSchemeOfIsRegularSection_section M' σ hreg)
  have hnv : Stacks.SheafOfModules.nonvanishingLocus (X := Z.toRingedSpace) M' σ =
      (zeroScheme Z M' (σ.eval (op ⊤))).supportSetᶜ :=
    (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap Z.toRingedSpace
      (invertibleSheafIsoZeroSchemeOfIsRegularSection M' σ hreg) σ).symm.trans
        ((congrArg (Stacks.SheafOfModules.nonvanishingLocus (X := Z.toRingedSpace)
          (Stacks.Divisors.invertibleSheaf' (zeroScheme Z M' (σ.eval (op ⊤))))) hsec).trans
            (Stacks.Divisors.nonvanishingChart_canonicalSections
              (zeroScheme Z M' (σ.eval (op ⊤)))))
  have hnv' : Stacks.Ample.nonvanishingLocus M' s' =
      (zeroScheme Z M' (σ.eval (op ⊤))).supportSetᶜ := by
    rwa [← hσ, ← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Z M' σ]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.IdealSheafData.range_subschemeι]
  change i '' (zeroScheme Z M' (σ.eval (op ⊤))).supportSet = _
  rw [← compl_compl (zeroScheme Z M' (σ.eval (op ⊤))).supportSet, ← hnv', ← hpre,
    ← Set.preimage_compl, Set.image_preimage_eq_range_inter, Set.inter_comm]

variable {k : Type u} [Field k]

/-- A closed subscheme of a scheme proper over a field has finitely many associated points. -/
private theorem finite_schemeAssociatedPoints (g : Z ⟶ Spec (.of k)) [IsProper g] :
    (Stacks.Divisors.schemeAssociatedPoints Z).Finite := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  exact associatedPoints_finite _

/-- **One cut in the intersection number** ([Stacks, Tag 0BEU] with a tensor power): if
`M ≅ 𝓛₁^{⊗n}` and `D ⊆ Z` is an effective Cartier divisor with `𝒪_Z(D) ≅ M|_Z`, then
`n (𝓛₁ ⋯ 𝓛_{d+1} · Z) = (𝓛₂ ⋯ 𝓛_{d+1} · D)`. -/
private theorem natCast_mul_intersectionNumber_eq (g : Y ⟶ Spec (.of k)) [IsProper g]
    (i : Z ⟶ Y) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ))
    (L : Fin (d + 1) → Y.Modules)
    [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)] (n : ℕ)
    (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (M₀ : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M₀]
    (hM₀ : L 0 = M₀)
    (e : M ≅ Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 M₀ n)
    (Dv : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Dv]
    (eD : (Scheme.Modules.pullback i).obj M ≅ Stacks.Divisors.invertibleSheaf Dv) :
    (n : ℤ) * intersectionNumber k g i (d + 1) hd L =
      intersectionNumber k g (Dv.subschemeι ≫ i) d
        (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k g i d hd Dv)
        (fun t => L t.succ) := by
  classical
  subst hM₀
  have : ∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (Function.update L 0
      (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 (L 0) n) t) :=
    isInvertible_update L 0 _
  rw [← intersectionNumber_update_tensorPower k g i (d + 1) hd L 0 n]
  have hL : (Scheme.Modules.pullback i).obj (Function.update L 0
      (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 (L 0) n) 0) ≅
        Stacks.Divisors.invertibleSheaf Dv :=
    eqToIso (congrArg (Scheme.Modules.pullback i).obj (Function.update_self _ _ _)) ≪≫
      (Scheme.Modules.pullback i).mapIso e.symm ≪≫ eD
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k g i d hd _ Dv hL]
  congr 1

/-- An invertible module `M` *has nonvanishing powers* if every finite set of points lies in the
nonvanishing locus of a global section of some positive tensor power `M^{⊗ n}`. Ample modules
have this property ([Stacks, Tag 09NV]), and it is preserved by pull-back. -/
private def HasNonvanishingPowers (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] :
    Prop :=
  ∀ T : Set Y, T.Finite → ∃ n : ℕ, 1 ≤ n ∧
    ∃ (N : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y N)
    (_ : Nonempty
      (N ≅ Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 M n))
    (s : Γ(N, ⊤)), T ⊆ Stacks.Ample.nonvanishingLocus N s

/-- The power `Stacks.Ample.tensorPowModule Y M n` is isomorphic to the tensor power `M^{⊗ n}`
used by the intersection numbers. -/
private noncomputable def tensorPowModuleIsoTensorPower (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (n : ℤ) : Stacks.Ample.tensorPowModule Y M n ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 M n :=
  (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Y M n).symm

/-- An ample invertible module has nonvanishing powers ([Stacks, Tag 09NV]). -/
private theorem hasNonvanishingPowers_of_isAmple (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Scheme.Modules.IsAmple Y M) :
    HasNonvanishingPowers M := by
  intro T hT
  obtain ⟨n, hn, s, -, hTs, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple Y M hM) hT ⊤ (fun _ _ => trivial)
  exact ⟨n, hn, _, inferInstance, ⟨tensorPowModuleIsoTensorPower M n⟩, s,
    hTs.trans (Stacks.AmpleTheory.coe_powNonvanishingOpen Y M n s).le⟩

/-- The pull-back of a tensor power is the tensor power of the pull-back. -/
private noncomputable def pullbackTensorPowerIso {X V : Scheme.{u}} (f : X ⟶ V) (A : V.Modules)
    [Stacks.Ample.IsInvertibleModule V A] (n : ℕ) :
    (Scheme.Modules.pullback f).obj
        (Stacks.SheafOfModules.Invertible.tensorPower V.presheaf V.ringCatSheaf.2 A n) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        ((Scheme.Modules.pullback f).obj A) n :=
  (Scheme.Modules.pullback f).mapIso (tensorPowModuleIsoTensorPower A n).symm ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f A n ≪≫
    tensorPowModuleIsoTensorPower ((Scheme.Modules.pullback f).obj A) n

private theorem HasNonvanishingPowers.of_eq {M M' : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y M] [Stacks.Ample.IsInvertibleModule Y M'] (h : M = M')
    (hM : HasNonvanishingPowers M) : HasNonvanishingPowers M' := by
  subst h
  exact hM

/-- The pull-back of a module with nonvanishing powers has nonvanishing powers. -/
private theorem HasNonvanishingPowers.pullback {X V : Scheme.{u}} (f : X ⟶ V) (A : V.Modules)
    [Stacks.Ample.IsInvertibleModule V A] (hA : HasNonvanishingPowers A) :
    HasNonvanishingPowers ((Scheme.Modules.pullback f).obj A) := by
  intro T hT
  obtain ⟨n, hn, N, _, ⟨e⟩, s, hs⟩ := hA (f '' T) (hT.image _)
  refine ⟨n, hn, (Scheme.Modules.pullback f).obj N, inferInstance,
    ⟨(Scheme.Modules.pullback f).mapIso e ≪≫ pullbackTensorPowerIso f A n⟩,
    (pullbackGlobalSections f N).hom s, ?_⟩
  rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections f N s]
  exact fun x hx => hs ⟨x, hx, rfl⟩

/-- **One cut by a module with nonvanishing powers.** For a closed subscheme `Z` of a proper
`k`-scheme `Y` and a family whose first member has nonvanishing powers, there is an effective
Cartier divisor `D ⊆ Z` with
`n (𝓛₁ ⋯ 𝓛_{d+1} · Z) = (𝓛₂ ⋯ 𝓛_{d+1} · D)` for some `n ≥ 1`. The divisor depends only on the
first member, so the identity holds for every choice of the others. -/
private theorem exists_cut_of_hasNonvanishingPowers (g : Y ⟶ Spec (.of k)) [IsProper g]
    (i : Z ⟶ Y) [IsClosedImmersion i] (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (hM : HasNonvanishingPowers M) :
    ∃ (n : ℕ) (Dv : Z.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor Dv),
      1 ≤ n ∧ Set.range (Dv.subschemeι ≫ i) ⊆ Set.range i ∧
      ∀ (d : ℕ) (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → Y.Modules)
        [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)]
        (L' : Fin d → Y.Modules)
        [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L' t)], L 0 = M →
        (∀ t, L t.succ = L' t) →
        (n : ℤ) * intersectionNumber k g i (d + 1) hd L =
          intersectionNumber k g (Dv.subschemeι ≫ i) d
            (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k g i d
              hd Dv) L' := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ g)
  obtain ⟨n, hn, N, _, ⟨e⟩, s, hs⟩ := hM (i '' Stacks.Divisors.schemeAssociatedPoints Z)
    ((finite_schemeAssociatedPoints (i ≫ g)).image _)
  obtain ⟨Dv, hDv, ⟨eD⟩, hrange⟩ := exists_cut i N s fun z hz => hs ⟨z, hz, rfl⟩
  refine ⟨n, Dv, hDv, hn, hrange ▸ Set.inter_subset_left, fun d hd L _ L' _ hL0 hL' => ?_⟩
  subst hL0
  rw [natCast_mul_intersectionNumber_eq g i d hd L n N (L 0) rfl e Dv eD]
  congr 1
  exact funext hL'

/-- Intersection numbers of a family of invertible modules with nonvanishing powers, on a closed
subscheme of a proper `k`-scheme, are nonnegative. -/
private theorem intersectionNumber_nonneg_of_hasNonvanishingPowers (g : Y ⟶ Spec (.of k))
    [IsProper g] :
    ∀ (d : ℕ) {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
      (hd : topologicalKrullDim Z ≤ (d : ℕ)) (L : Fin d → Y.Modules)
      [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)],
      (∀ t, HasNonvanishingPowers (L t)) → 0 ≤ intersectionNumber k g i d hd L
  | 0, Z, i, _, hd, L, _, _ => by
    rw [intersectionNumber_zero_eq_finrank_globalSections]
    exact Nat.cast_nonneg _
  | d + 1, Z, i, _, hd, L, _, hL => by
    obtain ⟨n, Dv, hDv, hn, -, hcut⟩ :=
      exists_cut_of_hasNonvanishingPowers g i (L 0) (hL 0)
    have h0 := intersectionNumber_nonneg_of_hasNonvanishingPowers g d (Dv.subschemeι ≫ i)
      (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k g i d hd Dv)
      (fun t => L t.succ) (fun t => hL t.succ)
    rw [← hcut d hd L (fun t => L t.succ) rfl fun _ => rfl] at h0
    exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast hn)

/-- **Cutting by an effective Cartier divisor.** On an integral scheme `Y` proper over `k`, if
the first member of the family is `𝒪_Y(E)` for an effective Cartier divisor `E` and the others
have nonvanishing powers, the intersection number is nonnegative: the canonical section of
`𝒪_Y(E)` is regular, so `(𝒪_Y(E) · 𝓛₂ ⋯ 𝓛_{d+1} · Y) = (𝓛₂ ⋯ 𝓛_{d+1} · E)`. -/
private theorem intersectionNumber_nonneg_of_isEffective [IsIntegral Y] (g : Y ⟶ Spec (.of k))
    [IsProper g] (d : ℕ) (hd : topologicalKrullDim Y ≤ (d + 1 : ℕ))
    (L : Fin (d + 1) → Y.Modules)
    [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)]
    (E : Y.CartierDivisor) (hE : MMP.Intersection.IsEffective E)
    (hL0 : L 0 = MMP.CartierDivisor.sheaf E)
    (hL : ∀ t : Fin d, HasNonvanishingPowers (L t.succ)) :
    0 ≤ intersectionNumber k g (𝟙 Y) (d + 1) hd L := by
  set M := MMP.CartierDivisor.sheaf E
  have hinv : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M :=
    MMP.Mori.isInvertible_cartierSheaf E
  set σ := Stacks.SheafOfModules.sectionsOfTop M (MMP.CartierDivisor.canonicalSection E hE)
  have hσ : σ.eval (op ⊤) = MMP.CartierDivisor.canonicalSection E hE :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ _
  have hne : σ.eval (op ⊤) ≠ 0 := by
    rw [hσ]
    intro h0
    have h1 := congrArg Subtype.val h0
    change (1 : Y.totalQuotientSheaf.obj.obj (op ⊤)) = 0 at h1
    have h2 : MMP.CartierDivisorSheaf.toK (X := Y) ⊤ 1 =
        MMP.CartierDivisorSheaf.toK (X := Y) ⊤ 0 := by
      rwa [map_one, map_zero]
    exact one_ne_zero (MMP.CartierDivisorSheaf.toK_injective ⊤ h2)
  have hreg := isRegularSection_of_eval_top_ne_zero M σ hne
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme Y M (σ.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y M σ).mpr hreg
  have eD : (Scheme.Modules.pullback (𝟙 Y)).obj M ≅
      Stacks.Divisors.invertibleSheaf (zeroScheme Y M (σ.eval (op ⊤))) :=
    (Scheme.Modules.pullbackId Y).app M ≪≫ invertibleSheafIsoZeroSchemeOfIsRegularSection M σ hreg
  have e : M ≅ Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 M
      ((1 : ℕ) : ℤ) :=
    (Stacks.SheafOfModules.Invertible.tensorPowerOneIso Y.presheaf Y.ringCatSheaf.2 M).symm
  have h0 := intersectionNumber_nonneg_of_hasNonvanishingPowers g d
    ((zeroScheme Y M (σ.eval (op ⊤))).subschemeι ≫ 𝟙 Y)
    (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k g (𝟙 Y) d hd
      (zeroScheme Y M (σ.eval (op ⊤)))) (fun t => L t.succ) hL
  rwa [← natCast_mul_intersectionNumber_eq g (𝟙 Y) d hd L 1 M M hL0 e _ eD, Nat.cast_one,
    one_mul] at h0

/-- `intersectionNumber_nonneg_of_isEffective` with `𝒪_Y(E)` in an arbitrary position, by the
symmetry of the intersection number. -/
private theorem intersectionNumber_nonneg_of_isEffective' [IsIntegral Y] (g : Y ⟶ Spec (.of k))
    [IsProper g] (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : ℕ)) (L : Fin d → Y.Modules)
    [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)] (j : Fin d)
    (E : Y.CartierDivisor) (hE : MMP.Intersection.IsEffective E)
    (hLj : L j = MMP.CartierDivisor.sheaf E)
    (hL : ∀ t, t ≠ j → HasNonvanishingPowers (L t)) :
    0 ≤ intersectionNumber k g (𝟙 Y) d hd L := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by have := j.pos; omega⟩
  rw [← intersectionNumber_comp_perm k g (𝟙 Y) (d + 1) hd L (Equiv.swap 0 j)]
  refine intersectionNumber_nonneg_of_isEffective g d hd _ E hE
    (by rw [Equiv.swap_apply_left, hLj]) fun t => hL _ ?_
  rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  exact Fin.succ_ne_zero t

end Cut

section Family

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- The family `(B, …, B, H, …, H, L)` with `b` copies of `B` followed by `h` copies of `H`. The
length is written `(h + 1) + b`, so that removing the first member — a `B` when `b > 0` — gives
the family of length `(h + 1) + (b - 1)` definitionally. -/
private def fam (B H L : Y.Modules) (b h : ℕ) : Fin ((h + 1) + b) → Y.Modules :=
  fun t => if (t : ℕ) < b then B else if (t : ℕ) < b + h then H else L

private theorem isInvertible_fam (B H L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (b h : ℕ) (t : Fin ((h + 1) + b)) :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (fam B H L b h t) := by
  unfold fam
  split_ifs <;> infer_instance

private theorem fam_zero_left (B H L : Y.Modules) (b h : ℕ) : fam B H L (b + 1) h 0 = B := by
  simp [fam]

private theorem fam_succ_left (B H L : Y.Modules) (b h : ℕ) :
    (fun t : Fin ((h + 1) + b) => fam B H L (b + 1) h t.succ) = fam B H L b h := by
  funext t
  simp only [fam, Fin.val_succ]
  split_ifs <;> first | rfl | omega

private theorem fam_zero_right (B H L : Y.Modules) (h : ℕ) : fam B H L 0 (h + 1) 0 = H := by
  simp [fam]

private theorem fam_succ_right (B H L : Y.Modules) (h : ℕ) :
    (fun t : Fin (h + 1) => fam B H L 0 (h + 1) t.succ) = fam B H L 0 h := by
  funext t
  simp only [fam, Fin.val_succ]
  split_ifs <;> first | rfl | omega

private theorem fam_self (B H : Y.Modules) (h : ℕ) : fam B H H 0 h = fun _ => H := by
  funext t
  simp only [fam]
  split_ifs <;> first | rfl | omega

private theorem fam_last (B H L : Y.Modules) (b h : ℕ) :
    fam B H L b h ⟨h + b, by omega⟩ = L := by
  simp only [fam]
  split_ifs <;> first | rfl | omega

private theorem fam_ne_last (B H L : Y.Modules) (b h : ℕ) (t : Fin ((h + 1) + b))
    (ht : t ≠ ⟨h + b, by omega⟩) : fam B H L b h t = B ∨ fam B H L b h t = H := by
  have ht' : (t : ℕ) ≠ h + b := fun h' => ht (Fin.ext h')
  simp only [fam]
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

end Family

attribute [local instance] isInvertible_fam

section Stages

variable {k : Type u} [Field k]

/-- **Cutting by the second module.** A closed subscheme `Z` of dimension at most `h + 1` of a
proper `k`-scheme `Y` contains a closed subscheme `Z'` of dimension at most one such that, for a
fixed `N ≥ 1` and every invertible `L`, `N (H^h · L · Z) = (L · Z')`. -/
private theorem exists_cut_right {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g]
    (B H : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H] (hH : HasNonvanishingPowers H) :
    ∀ (h : ℕ) {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
      (hd : topologicalKrullDim Z ≤ (h + 1 : ℕ)),
      ∃ (Z' : Scheme.{u}) (i' : Z' ⟶ Y) (_ : IsClosedImmersion i')
        (hd' : topologicalKrullDim Z' ≤ (1 : ℕ)) (N : ℕ), 1 ≤ N ∧ Set.range i' ⊆ Set.range i ∧
        ∀ (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L],
          (N : ℤ) * intersectionNumber k g i (h + 1) hd (fam B H L 0 h) =
            intersectionNumber k g i' 1 hd' (fun _ => L)
  | 0, Z, i, _, hd => ⟨Z, i, inferInstance, hd, 1, le_rfl, le_rfl, fun L _ => by
      rw [Nat.cast_one, one_mul]
      congr 1⟩
  | h + 1, Z, i, _, hd => by
    obtain ⟨n, Dv, hDv, hn, hsub, hcut⟩ :=
      exists_cut_of_hasNonvanishingPowers g i H hH
    obtain ⟨Z', i', hi', hd', N, hN, hsub', hL⟩ := exists_cut_right g B H hH h (Dv.subschemeι ≫ i)
      (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k g i (h + 1)
        hd Dv)
    refine ⟨Z', i', hi', hd', n * N, one_le_mul hn hN,
      hsub'.trans hsub, fun L _ => ?_⟩
    rw [← hL L, ← hcut (h + 1) hd (fam B H L 0 (h + 1)) (fam B H L 0 h)
      (fam_zero_right B H L h) (congrFun (fam_succ_right B H L h))]
    push_cast
    ring

/-- **Cutting by pull-backs from the base.** Let `f : X ⟶ V` be a morphism of proper `k`-schemes,
`A` a module on `V` with nonvanishing powers, `Y ⊆ V` and `Z = f⁻¹(Y) ⊆ X` closed subschemes of
dimensions at most `b` and `h + 1 + b`. Cutting `Y` by `b` sections of powers of `A` and `Z` by
their pull-backs gives closed subschemes `Y'` of dimension at most zero and `Z' = f⁻¹(Y')` of
dimension at most `h + 1`, with `N (A^b · Y)` equal to the zero-dimensional intersection number
of `Y'` and `N' ((f^*A)^b H^h L · Z) = (H^h L · Z')` for every invertible `L`. -/
private theorem exists_cut_left {X V : Scheme.{u}} (gX : X ⟶ Spec (.of k)) [IsProper gX]
    (gV : V ⟶ Spec (.of k)) [IsProper gV] (f : X ⟶ V) (A : V.Modules)
    [Stacks.Ample.IsInvertibleModule V A] (hA : HasNonvanishingPowers A) (H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] (h : ℕ) :
    ∀ (b : ℕ) {Y Z : Scheme.{u}} (ι : Y ⟶ V) [IsClosedImmersion ι] (i : Z ⟶ X)
      [IsClosedImmersion i] (hY : topologicalKrullDim Y ≤ (b : ℕ))
      (hZ : topologicalKrullDim Z ≤ ((h + 1) + b : ℕ)), Set.range i = f ⁻¹' Set.range ι →
      ∃ (Y' : Scheme.{u}) (ι' : Y' ⟶ V) (_ : IsClosedImmersion ι')
        (hY' : topologicalKrullDim Y' ≤ (0 : ℕ)) (Z' : Scheme.{u}) (i' : Z' ⟶ X)
        (_ : IsClosedImmersion i') (hZ' : topologicalKrullDim Z' ≤ (h + 1 : ℕ)) (N N' : ℕ),
        1 ≤ N ∧ Set.range i' = f ⁻¹' Set.range ι' ∧
        (N : ℤ) * intersectionNumber k gV ι b hY (fun _ => A) =
          intersectionNumber k gV ι' 0 hY' (fun _ => A) ∧
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
          (N' : ℤ) * intersectionNumber k gX i ((h + 1) + b) hZ
              (fam ((Scheme.Modules.pullback f).obj A) H L b h) =
            intersectionNumber k gX i' (h + 1) hZ'
              (fam ((Scheme.Modules.pullback f).obj A) H L 0 h)
  | 0, Y, Z, ι, _, i, _, hY, hZ, hYZ => ⟨Y, ι, inferInstance, hY, Z, i, inferInstance, hZ, 1, 1,
      le_rfl, hYZ, by rw [Nat.cast_one, one_mul], fun L _ => by rw [Nat.cast_one, one_mul]⟩
  | b + 1, Y, Z, ι, _, i, _, hY, hZ, hYZ => by
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ gV)
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ gX)
    obtain ⟨n, hn, MV, _, ⟨e⟩, s, hs⟩ := hA (ι '' Stacks.Divisors.schemeAssociatedPoints Y ∪
        f '' (i '' Stacks.Divisors.schemeAssociatedPoints Z))
      (((finite_schemeAssociatedPoints (ι ≫ gV)).image _).union
        (((finite_schemeAssociatedPoints (i ≫ gX)).image _).image _))
    obtain ⟨DY, hDY, ⟨eDY⟩, hrY⟩ := exists_cut ι MV s
      fun y hy => hs (Or.inl ⟨y, hy, rfl⟩)
    have hpre := Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections f
      MV s
    obtain ⟨DZ, hDZ, ⟨eDZ⟩, hrZ⟩ := exists_cut i ((Scheme.Modules.pullback f).obj MV)
        ((pullbackGlobalSections f MV).hom s) fun z hz => by
      rw [← hpre]
      exact hs (Or.inr ⟨i z, ⟨z, hz, rfl⟩, rfl⟩)
    have hYZ' : Set.range (DZ.subschemeι ≫ i) = f ⁻¹' Set.range (DY.subschemeι ≫ ι) := by
      rw [hrZ, hrY, hYZ, ← hpre, Set.preimage_inter, Set.preimage_compl]
    obtain ⟨Y', ι', hι', hY', Z', i', hi', hZ', N, N', hN, hYZ'', hV, hX⟩ :=
      exists_cut_left gX gV f A hA H h b (DY.subschemeι ≫ ι) (DZ.subschemeι ≫ i)
        (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k gV ι b hY DY)
        (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k gX i
          ((h + 1) + b) hZ DZ) hYZ'
    refine ⟨Y', ι', hι', hY', Z', i', hi', hZ', n * N, n * N', one_le_mul hn hN,
      hYZ'', ?_, fun L _ => ?_⟩
    · rw [← hV, ← natCast_mul_intersectionNumber_eq gV ι b hY (fun _ => A) n MV A rfl e DY eDY]
      push_cast
      ring
    · have h1 := natCast_mul_intersectionNumber_eq gX i ((h + 1) + b) hZ
        (fam ((Scheme.Modules.pullback f).obj A) H L (b + 1) h) n _
        ((Scheme.Modules.pullback f).obj A) (fam_zero_left _ _ _ _ _)
        ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackTensorPowerIso f A n) DZ eDZ
      rw [← hX L]
      have h2 : intersectionNumber k gX (DZ.subschemeι ≫ i) ((h + 1) + b)
          (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k gX i
            ((h + 1) + b) hZ DZ)
          (fun t => fam ((Scheme.Modules.pullback f).obj A) H L (b + 1) h t.succ) =
          intersectionNumber k gX (DZ.subschemeι ≫ i) ((h + 1) + b)
          (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k gX i
            ((h + 1) + b) hZ DZ) (fam ((Scheme.Modules.pullback f).obj A) H L b h) := by
        congr 1
        exact fam_succ_left _ _ _ _ _
      rw [← h2, ← h1]
      push_cast
      rw [mul_comm (n : ℤ) (N' : ℤ), mul_assoc]
      rfl

end Stages

section Geometry

/-- In a `T₀` space of dimension at most zero every point is closed: a proper specialization
`y ⤳ z` would give the chain `{z}⁻ ⊊ {y}⁻` of irreducible closed sets. -/
private theorem isClosed_singleton_of_topologicalKrullDim_le_zero {T : Type*} [TopologicalSpace T]
    [T0Space T] (h : topologicalKrullDim T ≤ 0) (y : T) : IsClosed ({y} : Set T) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_contra hzy
  have hlt : (⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      TopologicalSpace.IrreducibleCloseds T) <
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure {z} ⊆ closure {y}
      exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure
    · intro heq
      have h1 : closure ({z} : Set T) = closure {y} :=
        congrArg (fun s : TopologicalSpace.IrreducibleCloseds T => (s : Set T)) heq
      exact hzy (Inseparable.eq (inseparable_iff_closure_eq.mpr h1))
  have : 0 < topologicalKrullDim T := by
    unfold topologicalKrullDim
    exact Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩
  exact absurd h (not_le.mpr this)

variable {k : Type u} [Field k]

/-- A closed subscheme `Z ⊆ X` containing a whole fibre of a surjective morphism of varieties
`f : X ⟶ V` has `dim X ≤ dim Z + dim V`: every component of a fibre has dimension at least
`dim X - dim V`. -/
private theorem topologicalKrullDim_le_add_of_preimage_subset {X V Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pV : V ⟶ Spec (.of k)) [IsVariety k pX] [IsVariety k pV]
    (f : X ⟶ V) (hf : f ≫ pV = pX) (hsurj : Function.Surjective f) (i : Z ⟶ X)
    [IsClosedImmersion i] (y : V) (hy : f ⁻¹' {y} ⊆ Set.range i) :
    topologicalKrullDim X ≤ topologicalKrullDim Z + topologicalKrullDim V := by
  have : Surjective f := ⟨hsurj⟩
  obtain ⟨x, rfl⟩ := hsurj y
  have hmem := irreducibleComponent_mem_irreducibleComponents (f.asFiber x)
  have h1 := (MMP.topologicalKrullDim_fiber_of_isDominant k pX pV f hf).1 (f x) _ hmem
  refine h1.trans (add_le_add_left ?_ _)
  have h2 : topologicalKrullDim (irreducibleComponent (f.asFiber x)) ≤
      topologicalKrullDim (f.fiber (f x)) :=
    Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  have h3 : topologicalKrullDim (f.fiber (f x)) ≤ topologicalKrullDim (f ⁻¹' {f x}) :=
    (f.fiberHomeo (f x)).isInducing.topologicalKrullDim_le
  have h4 : topologicalKrullDim (f ⁻¹' {f x}) ≤ topologicalKrullDim (Set.range i) :=
    (Topology.IsEmbedding.inclusion hy).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_eq i] at h4
  exact h2.trans (h3.trans h4)

/-- An integral scheme locally of finite type over a field has finite, natural, dimension. -/
private theorem exists_nat_topologicalKrullDim_eq {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IsIntegral X] : ∃ n : ℕ, topologicalKrullDim X = n := by
  have h := topologicalKrullDim_lt_top_of_isIntegral k f (𝟙 X)
  have hbot : topologicalKrullDim X ≠ ⊥ := fun hb =>
    ((topologicalKrullDim_eq_bot_iff_isEmpty X).mp hb).false (Classical.arbitrary X)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
  induction a using ENat.recTopCoe with
  | top =>
    rw [← ha] at h
    exact absurd h (lt_irrefl _)
  | coe a => exact ⟨a, ha.symm⟩

/-- **The one-dimensional components of a curve-like closed subscheme** ([Stacks, Tag 0BES]).
If `Z ⊆ X` is a closed subscheme of dimension one of a proper `k`-scheme, there are finitely
many proper curves `Cⱼ ⊆ Z` and positive integers `mⱼ` with `(L · Z) = ∑ mⱼ deg_{Cⱼ} L` for
every invertible `L`. -/
private theorem exists_properCurves {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (i : Z ⟶ X) [IsClosedImmersion i] (hZ : topologicalKrullDim Z = (1 : ℕ)) :
    ∃ (ι : Type u) (_ : Fintype ι) (C : ι → MMP.Mori.ProperCurve sX) (m : ι → ℤ),
      (∀ j, 0 < m j) ∧ (∀ j, closure {(C j).point} ⊆ Set.range i) ∧
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        intersectionNumber k sX i 1 hZ.le (fun _ => L) = ∑ j, m j * (C j).degree k L := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  set F := (Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)
  have : Finite (TopDimIntegralSubscheme F) := finite_topDimIntegralSubscheme k sX F
  let _ : Fintype (TopDimIntegralSubscheme F) := Fintype.ofFinite _
  have : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ sX)
  have : F.IsCoherent := isCoherent_pushforward_of_isClosedImmersion i _
  have hsupp : _root_.SheafOfModules.supp F = Set.range i :=
    Stacks.Chow.supp_pushforwardStructureSheaf i
  have hcl : ∀ W : TopDimIntegralSubscheme F,
      (W.1.support : Set X) = closure {W.genericPt} := fun W => by
    have := W.2.1
    rw [← W.1.range_subschemeι, TopDimIntegralSubscheme.genericPt, ← Set.image_singleton,
      W.1.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_spec W.1.subscheme,
      Set.image_univ]
  have hW : ∀ W : TopDimIntegralSubscheme F,
      W.1 = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {W.genericPt}) :=
    fun W => by
    have := W.2.1
    have h := Stacks.Chow.ker_eq_vanishingIdeal_support_of_isReduced W.1.subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι] at h
    refine h.trans (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    exact hcl W
  have hWdim : ∀ W : TopDimIntegralSubscheme F,
      topologicalKrullDim W.1.subscheme = ((1 : ℕ) : WithBot ℕ∞) := fun W => by
    rw [W.2.2.2, hsupp, topologicalKrullDim_range_eq i, hZ]
  let C : TopDimIntegralSubscheme F → MMP.Mori.ProperCurve sX := fun W =>
    ⟨W.genericPt, ⟨by rw [MMP.Mori.curveSubschemeAt, ← hW W, hWdim W]; rfl, inferInstance⟩⟩
  refine ⟨TopDimIntegralSubscheme F, inferInstance, C,
    fun W => Stacks.Chow.sheafMultiplicity F W.genericPt,
    fun W => sheafMultiplicity_genericPt_pos k sX F W, fun W => ?_, fun L _ => ?_⟩
  · change closure {W.genericPt} ⊆ _
    rw [← hcl W, ← hsupp]
    exact W.2.2.1
  · rw [intersectionNumber_eq_sum_topDimComponents k sX i 1 hZ (fun _ => L),
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun W _ => congrArg _ ?_
    rw [intersectionNumber_congr_ideal k sX (hW W) 1 _ (C W).dim_le (fun _ => L),
      intersectionNumber_one_eq_invertibleCurveDegree]
    rfl

/-- If a closed subscheme `Z ⊆ X` of dimension at most `h + 1` contains a fibre of a surjection
`f : X ⟶ V` of varieties with `dim X = h + 1 + dim V`, then `dim Z = h + 1`. -/
private theorem topologicalKrullDim_eq_of_preimage_subset {X V Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pV : V ⟶ Spec (.of k)) [IsVariety k pX] [IsVariety k pV]
    (f : X ⟶ V) (hf : f ≫ pV = pX) (hsurj : Function.Surjective f) (i : Z ⟶ X)
    [IsClosedImmersion i] (y : V) (hy : f ⁻¹' {y} ⊆ Set.range i) {h v : ℕ}
    (hX : topologicalKrullDim X = ((h + 1 + v : ℕ) : WithBot ℕ∞))
    (hV : topologicalKrullDim V = (v : WithBot ℕ∞))
    (hZ : topologicalKrullDim Z ≤ ((h + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim Z = ((h + 1 : ℕ) : WithBot ℕ∞) := by
  have hle := topologicalKrullDim_le_add_of_preimage_subset pX pV f hf hsurj i y hy
  have : Nonempty Z := by
    obtain ⟨x, hx⟩ := hsurj y
    obtain ⟨z, -⟩ := hy hx
    exact ⟨z⟩
  obtain ⟨a, ha, -⟩ := exists_nat_topologicalKrullDim_eq_of_lt (T := Z) (n := h + 2)
    (lt_of_le_of_lt hZ (by exact_mod_cast (by omega : h + 1 < h + 2)))
  rw [ha] at hZ ⊢
  rw [hX, ha, hV] at hle
  have h1 : a ≤ h + 1 := by exact_mod_cast hZ
  have h2 : (h + 1) + v ≤ a + v := by exact_mod_cast hle
  congr 1
  omega

end Geometry

section Separation

variable {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (F : X ⟶ T)

/-- **A moving curve class excludes pseudo-effectivity.** If finitely many curves `Cⱼ`
contracted by `F`, with weights `mⱼ ≥ 0`, satisfy `∑ mⱼ (E · Cⱼ) ≥ 0` for every effective Cartier
divisor `E` and `∑ mⱼ (D · Cⱼ) < 0`, then `D` is not pseudo-effective over `T`: the form
`z ↦ ∑ mⱼ (z · Cⱼ)` is continuous on `N¹(X/T)`, nonnegative on the effective cone and hence on
its closure. -/
private theorem not_isRelativelyPseudoEffective_of_sum {ι : Type*} [Fintype ι]
    (C : ι → MMP.Mori.ProperCurve sX) (hC : ∀ j, (C j).IsContractedBy F) (m : ι → ℝ)
    (hE : ∀ E : X.CartierDivisor, MMP.Intersection.IsEffective E →
      0 ≤ ∑ j, m j * ((C j).degree k (MMP.CartierDivisor.sheaf E) : ℝ))
    (D : MMP.Mori.KCartierDivisor ℝ X)
    (hD : ∑ j, m j * ((C j).cycle ℝ).intersectionNumber D < 0) :
    ¬ MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective sX F D := by
  intro hpe
  set q := (LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX F)).liftQ
    (MMP.Fourfold.relativeDegreeMap sX F) le_rfl
  let Λ : MMP.Fourfold.RelativeNumericalDivisorClasses sX F →ₗ[ℝ] ℝ :=
    (∑ j, m j • LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) ⟨C j, hC j⟩) ∘ₗ q
  have hΛx : ∀ x, Λ x = ∑ j, m j * q x ⟨C j, hC j⟩ := fun x => by
    simp only [Λ, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hΛ : ∀ D : MMP.Mori.KCartierDivisor ℝ X,
      Λ (MMP.Fourfold.relativeNumericalDivisorClass sX F D) =
        ∑ j, m j * ((C j).cycle ℝ).intersectionNumber D := by
    intro D
    rw [hΛx]
    rfl
  have hcont : Continuous Λ := by
    have hq : Continuous q := continuous_induced_dom
    have : (Λ : _ → ℝ) = fun x => ∑ j, m j * q x ⟨C j, hC j⟩ := funext hΛx
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply _).comp hq)
  have hcone : (MMP.Fourfold.relativeEffectiveCone sX F : Set _) ⊆ {x | 0 ≤ Λ x} := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => 0 ≤ Λ x) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨E, hEff, rfl⟩
      rw [hΛ]
      convert hE E hEff using 2 with j
      rw [MMP.Mori.OneCycle.intersectionNumber_ofCartier, MMP.Mori.OneCycle.cartierDegree,
        MMP.Mori.OneCycle.degree_cycle]
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_nonneg hx hy
    · intro c x _ hx
      change 0 ≤ Λ ((c : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  have hcl : closure (MMP.Fourfold.relativeEffectiveCone sX F : Set _) ⊆ {x | 0 ≤ Λ x} :=
    closure_minimal hcone (isClosed_le continuous_const hcont)
  have h := hcl hpe
  simp only [Set.mem_ofPred_eq, hΛ] at h
  linarith

/-- The degree of `𝒪_X(E)` along a proper curve is additive in the Cartier divisor `E`. -/
private theorem degree_sheaf_add (C : MMP.Mori.ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  rw [MMP.Mori.ProperCurve.degree, MMP.Mori.ProperCurve.degree, MMP.Mori.ProperCurve.degree,
    ← MMP.Mori.degreeOn_tensorSheaf]
  exact MMP.Mori.degreeOn_eq_of_iso k sX C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso E E').symm

/-- **The curves are negative on `D`.** If `-D = ∑ rᵢ Aᵢ` in `ℝ ⊗ Div(X)` with `rᵢ > 0` and
`Aᵢ` ample over `V`, then `∑ mⱼ (D · Cⱼ) < 0` for every nonempty family of curves `Cⱼ`
contracted by `f` with weights `mⱼ > 0`. -/
private theorem sum_intersectionNumber_neg {V : Scheme.{u}} (f : X ⟶ V) {ι : Type*} [Fintype ι]
    [Nonempty ι] (C : ι → MMP.Mori.ProperCurve sX) (hC : ∀ j, (C j).IsContractedBy f)
    (m : ι → ℝ) (hm : ∀ j, 0 < m j) (D : MMP.Mori.KCartierDivisor ℝ X)
    (hD : ∃ (n : ℕ) (r : Fin n → ℝ) (A : Fin n → X.CartierDivisor), 1 ≤ n ∧ (∀ i, 0 < r i) ∧
      (∀ i, MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf (A i))) ∧
      Finsupp.linearCombination ℝ (fun E : X.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] E) (-D) =
        ∑ i, r i ⊗ₜ[ℤ] A i) :
    ∑ j, m j * ((C j).cycle ℝ).intersectionNumber D < 0 := by
  classical
  obtain ⟨n, r, A, hn, hr, hA, hDA⟩ := hD
  let δ : X.CartierDivisor →+ ℝ :=
    AddMonoidHom.mk' (fun E => ∑ j, m j * ((C j).degree k (MMP.CartierDivisor.sheaf E) : ℝ))
      fun E E' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [degree_sheaf_add, Int.cast_add, mul_add]
  let ψ : ℝ ⊗[ℤ] X.CartierDivisor →ₗ[ℤ] ℝ :=
    TensorProduct.lift ((LinearMap.mul ℤ ℝ).compl₂ δ.toIntLinearMap)
  have hψ : ∀ (c : ℝ) (E : X.CartierDivisor), ψ (c • ((1 : ℝ) ⊗ₜ[ℤ] E)) = c * δ E := by
    intro c E
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact TensorProduct.lift.tmul _ _
  have hsum : ∑ j, m j * ((C j).cycle ℝ).intersectionNumber D =
      ψ (Finsupp.linearCombination ℝ (fun E : X.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] E) D) := by
    have hcyc : ∀ j, ((C j).cycle ℝ).intersectionNumber D = D.sum fun E c =>
        c * ((C j).degree k (MMP.CartierDivisor.sheaf E) : ℝ) := fun j => by
      rw [MMP.Mori.OneCycle.intersectionNumber_eq_sum]
      refine Finsupp.sum_congr fun E _ => ?_
      rw [MMP.Mori.ProperCurve.cycle, Finsupp.sum_single_index (by simp), one_mul]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [hψ, hcyc, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    simp only [δ, AddMonoidHom.mk'_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpos : 0 < ψ (Finsupp.linearCombination ℝ (fun E : X.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] E)
      (-D)) := by
    rw [hDA, map_sum]
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [show ψ (r i ⊗ₜ[ℤ] A i) = r i * δ (A i) from TensorProduct.lift.tmul _ _]
    refine mul_pos (hr i) (Finset.sum_pos (fun j _ => mul_pos (hm j) ?_) Finset.univ_nonempty)
    exact_mod_cast MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      _ (hA i) (C j) (hC j)
  rw [map_neg, map_neg] at hpos
  rw [hsum]
  linarith

end Separation

section Curves

variable {k : Type u} [Field k]

/-- A positive intersection number on a closed subscheme of dimension at most `d` forces the
dimension to be exactly `d`. -/
private theorem topologicalKrullDim_eq_of_intersectionNumber_pos {Y Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsProper g] (i : Z ⟶ Y) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : ℕ)) (L : Fin d → Y.Modules)
    [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L t)]
    (h : 0 < intersectionNumber k g i d hd L) : topologicalKrullDim Z = (d : ℕ) := by
  refine le_antisymm hd (not_lt.mp fun hlt => ?_)
  rw [intersectionNumber_eq_zero_of_topologicalKrullDim_lt k g i d hd hlt] at h
  exact lt_irrefl _ h

/-- A projective `k`-scheme carries an ample invertible module. -/
private theorem exists_isInvertibleModule_isAmple {W : Scheme.{u}} (sW : W ⟶ Spec (.of k))
    (hW : IsProjectiveMorphism sW) :
    ∃ (A : W.Modules) (_ : Stacks.Ample.IsInvertibleModule W A), Scheme.Modules.IsAmple W A := by
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨A, hA, hAa⟩ := exists_isAmple_of_isProjectiveMorphism sW M hMa hW
  exact ⟨A, hA, (Stacks.AmpleBridge.isAmple_iff_isAmple _ A).mp hAa⟩

/-- **A moving family of contracted curves.** Let `f : X ⟶ V` be a surjective morphism of
projective varieties over `k` with `dim V < dim X`. There is a nonempty finite family of proper
curves `Cⱼ ⊆ X` contracted by `f`, with weights `mⱼ > 0`, such that `∑ mⱼ (E · Cⱼ) ≥ 0` for every
effective Cartier divisor `E`. The curves are the one-dimensional components of
`(f^*A)^v · H^{n-v-1} · X` for ample `A` on `V` and `H` on `X`. -/
private theorem exists_contracted_curves {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sV : V ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsProjectiveVariety k sV] (f : X ⟶ V)
    (hfX : f ≫ sV = sX) (hsurj : Function.Surjective f)
    (hlt : topologicalKrullDim V < topologicalKrullDim X) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι) (C : ι → MMP.Mori.ProperCurve sX)
      (m : ι → ℤ), (∀ j, 0 < m j) ∧ (∀ j, (C j).IsContractedBy f) ∧
      ∀ E : X.CartierDivisor, MMP.Intersection.IsEffective E →
        0 ≤ ∑ j, m j * (C j).degree k (MMP.CartierDivisor.sheaf E) := by
  classical
  have : IsProper sX := isProper_of_isProjectiveMorphism sX IsProjectiveVariety.isProjective
  have : IsProper sV := isProper_of_isProjectiveMorphism sV IsProjectiveVariety.isProjective
  obtain ⟨A, _, hAamp⟩ :=
    exists_isInvertibleModule_isAmple sV IsProjectiveVariety.isProjective
  obtain ⟨H, _, hHamp⟩ :=
    exists_isInvertibleModule_isAmple sX IsProjectiveVariety.isProjective
  have hAg := hasNonvanishingPowers_of_isAmple A hAamp
  have hHg := hasNonvanishingPowers_of_isAmple H hHamp
  set B := (Scheme.Modules.pullback f).obj A
  have hBg : HasNonvanishingPowers B := HasNonvanishingPowers.pullback f A hAg
  obtain ⟨nX, hnX⟩ := exists_nat_topologicalKrullDim_eq sX
  obtain ⟨v, hv⟩ := exists_nat_topologicalKrullDim_eq sV
  obtain ⟨h0, rfl⟩ : ∃ h0, nX = (h0 + 1) + v := by
    have : v < nX := by
      rw [hnX, hv] at hlt
      exact_mod_cast hlt
    exact ⟨nX - v - 1, by omega⟩
  obtain ⟨Y', ι', hι', hY', Z₁, i₁, hi₁, hZ₁, N, N', hN, hr₁, hV₁, hX₁⟩ :=
    exists_cut_left sX sV f A hAg H h0 v (𝟙 V) (𝟙 X) hv.le hnX.le (by ext x; simp)
  have hdimY' := topologicalKrullDim_eq_of_intersectionNumber_pos sV ι' 0 hY' _ <| by
    rw [← hV₁]
    exact mul_pos (by exact_mod_cast hN)
      (intersectionNumber_pos k sV (𝟙 V) v hv (fun _ => A) fun _ => hAamp)
  obtain ⟨y₀⟩ : Nonempty Y' := not_isEmpty_iff.mp fun hY => WithBot.coe_ne_bot <|
    hdimY'.symm.trans ((topologicalKrullDim_eq_bot_iff_isEmpty Y').mpr hY)
  have hfib : f ⁻¹' {ι' y₀} ⊆ Set.range i₁ := by
    rw [hr₁]
    exact fun x hx => ⟨y₀, hx.symm⟩
  have hdimZ₁ :=
    topologicalKrullDim_eq_of_preimage_subset sX sV f hfX hsurj i₁ (ι' y₀) hfib hnX hv hZ₁
  obtain ⟨Z', i', hi', hd', N₂, hN₂, hsub', hX₂⟩ := exists_cut_right sX B H hHg h0 i₁ hZ₁
  have hposZ' : 0 < intersectionNumber k sX i' 1 hd' (fun _ => H) := by
    rw [← hX₂ H]
    refine mul_pos (by exact_mod_cast hN₂) ?_
    have e : intersectionNumber k sX i₁ (h0 + 1) hZ₁ (fam B H H 0 h0) =
        intersectionNumber k sX i₁ (h0 + 1) hdimZ₁.le (fun _ => H) := by
      congr 1
      exact fam_self B H h0
    rw [e]
    exact intersectionNumber_pos k sX i₁ (h0 + 1) hdimZ₁ (fun _ => H) fun _ => hHamp
  obtain ⟨ι, _, C, m, hm, hcl, hdeg⟩ := exists_properCurves sX i'
    (topologicalKrullDim_eq_of_intersectionNumber_pos sX i' 1 hd' _ hposZ')
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    rw [hdeg H, Finset.univ_eq_empty, Finset.sum_empty] at hposZ'
    exact lt_irrefl _ hposZ'
  refine ⟨ι, inferInstance, this, C, m, hm, fun j x hx => ?_, fun E hEff => ?_⟩
  · have hpt : (C j).point ∈ f ⁻¹' Set.range ι' := hr₁ ▸ hsub' (hcl j (subset_closure rfl))
    obtain ⟨q, hq⟩ := hpt
    have hclosed : IsClosed ({f (C j).point} : Set V) := by
      rw [← hq, ← Set.image_singleton]
      exact ι'.isClosedEmbedding.isClosedMap _
        (isClosed_singleton_of_topologicalKrullDim_le_zero hY' q)
    have h1 : f x ∈ closure {f (C j).point} :=
      map_mem_closure f.continuous hx fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact Set.mem_singleton _
    rwa [hclosed.closure_eq] at h1
  · have h1 := intersectionNumber_nonneg_of_isEffective' sX ((h0 + 1) + v) hnX.le
      (fam B H (MMP.CartierDivisor.sheaf E) v h0) ⟨h0 + v, by omega⟩ E hEff
      (fam_last _ _ _ _ _) fun t ht => by
        rcases fam_ne_last B H (MMP.CartierDivisor.sheaf E) v h0 t ht with h | h
        · exact HasNonvanishingPowers.of_eq h.symm hBg
        · exact HasNonvanishingPowers.of_eq h.symm hHg
    rw [← hdeg, ← hX₂, ← hX₁]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) h1)

end Curves

end MMP.FourfoldProofs.FourfoldNegativeFiberNotPseudoeffectiveProof

end

section

/-!
# A relatively anti-ample divisor of a fibre-type contraction is not pseudo-effective

Let `X → V → S` be projective morphisms of projective varieties over an algebraically closed
field `k` of characteristic zero, with `X` normal and `ℚ`-factorial and `f : X → V` a
contraction of fibre type (`dim V < dim X`). If `D` is a real Cartier divisor on `X` with `-D`
ample over `V`, then `D` is not pseudo-effective over `S`: a general complete-intersection curve
in a general fibre of `f` is a moving curve contracted to `S` on which `D` is negative, while
every effective real Cartier divisor is nonnegative on it.

## Main results

* `MMP.Fourfold.not_isRelativelyPseudoEffective_of_isFibreType`.

## Implementation notes

A real Cartier divisor is a formal combination `D : KCartierDivisor ℝ X`, and `-D` is ample over
`V` if, as an element of `ℝ ⊗[ℤ] Div(X)`, it is `∑ᵢ rᵢ Aᵢ` with at least one summand, all
`rᵢ > 0` and every Cartier divisor `Aᵢ` ample over `V` (`MMP.Mori.IsRelativelyAmple` of
`𝒪_X(Aᵢ)`). The equality is taken in the tensor product, so that it respects linear relations
among Cartier divisors. Pseudo-effectivity over `S` is
`MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective` for the composite `X → S`. The base
field is an algebraically closed field of characteristic zero rather than `ℂ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldNegativeFiberNotPseudoeffectiveProof in
/-- Let `X → V → S` be projective morphisms of projective varieties over an algebraically closed
field of characteristic zero, with `X` normal and `ℚ`-factorial and `f : X ⟶ V` a contraction of
fibre type. If `-D` is ample over `V`, i.e. `-D = ∑ᵢ rᵢ Aᵢ` in `ℝ ⊗[ℤ] Div(X)` with `rᵢ > 0` and
`Aᵢ` Cartier divisors ample over `V`, then `D` is not pseudo-effective over `S`. -/
@[mmp "lem_fourfold_negative_fiber_not_pseudoeffective"]
public theorem not_isRelativelyPseudoEffective_of_isFibreType
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X V S : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] [IsProjectiveVariety k sV] [IsProjectiveVariety k sS]
    [IsLocallyNoetherian X] [IsNormal X] (_hX : IsQFactorial sX)
    (f : X ⟶ V) (g : V ⟶ S) (hf : IsContraction sX sV f) (hft : hf.IsFibreType)
    (_hg : IsProjectiveMorphism g) (_hgs : g ≫ sS = sV)
    (D : MMP.Mori.KCartierDivisor ℝ X)
    (hD : ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → X.CartierDivisor), 1 ≤ m ∧ (∀ i, 0 < r i) ∧
      (∀ i, MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf (A i))) ∧
      Finsupp.linearCombination ℝ (fun E : X.CartierDivisor => (1 : ℝ) ⊗ₜ[ℤ] E) (-D) =
        ∑ i, r i ⊗ₜ[ℤ] A i) :
    ¬ KCartierDivisor.IsRelativelyPseudoEffective sX (f ≫ g) D := by
  obtain ⟨ι, _, _, C, m, hm, hC, hE⟩ :=
    exists_contracted_curves sX sV f hf.comp_eq hf.surjective hft
  exact not_isRelativelyPseudoEffective_of_sum sX (f ≫ g) C
    (fun j x hx => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC j x hx])
    (fun j => (m j : ℝ)) (fun E hEff => by exact_mod_cast hE E hEff) D
    (sum_intersectionNumber_neg sX f C hC (fun j => (m j : ℝ))
      (fun j => by exact_mod_cast hm j) D hD)

end MMP.Fourfold

end
