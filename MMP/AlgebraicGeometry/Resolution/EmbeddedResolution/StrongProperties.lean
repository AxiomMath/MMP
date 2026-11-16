module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Principalization.ComponentSmoothSingularLoci
public import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
public import MMP.AlgebraicGeometry.Resolution.Principalization.ComponentRestriction
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Resolution.Principalization

/-!
# Strong resolution properties of the embedded resolution (Kollár, *Resolution*, p. 146)

Let `X ⊆ A` be an admissible embedding of an affine disjoint union of varieties over a field `k`
of characteristic `0`, and let `Π : X_r → X` be the composite of the embedded resolution
`𝓑𝓡_A(X)`. Then `X_r` is smooth over `k`, `Π` is an isomorphism over the smooth locus `X^ns`,
and `Π⁻¹(Sing X)` is a divisor with simple normal crossings on `X_r`.

With `𝐁 = 𝓑𝓟^can(A, I_X, ∅)`, deleting empty blow-ups does not change the composite, and over a
connected component `C` of `X` (an open subscheme), with generic point `η_C` and entry index
`j_C = j_𝐁(η_C)`, the sequence `𝓑𝓡_𝐁(X ⊆ A)` pulls back to the restriction `(𝐁_{<j_C})|_C` of the
first `j_C` steps of `𝐁` to `C`. Hence `Π⁻¹(C) ≅ C_{j_C}` over `C`, and the three properties are
read off on each `C_{j_C}`:

1. `C_{j_C}` is smooth, being open and closed in the smooth centre `Z_{j_C}`;
2. the restricted composite is an isomorphism over a neighbourhood of every smooth point of `C`;
3. the preimage of `Sing C` in `C_{j_C}` is `C_{j_C} ∩ Ex_tot(Π_{j_C})`, a divisor with simple
   normal crossings; being snc is a condition at each point, so these glue on `X_r`.

## Main results

* `MMP.Resolution.isSmoothScheme_and_isIso_and_isSNCClosedSubset_embeddedResolution`

## Implementation notes

`X` is over `k` through its embedding, by `i ≫ s_A`. Characteristic `0`, affineness, and `X`
being a disjoint union of varieties are part of `IsAdmissibleEmbedding`. For a disjoint union of
varieties `X = ⨆_C C` the components `C` are open, so `⨆_C Sing C` and `⨆_C C^ns` are the
singular and smooth loci `MMP.Mori.singularLocus (i ≫ s_A)` and `MMP.Mori.smoothLocus (i ≫ s_A)`
of `X` over `k`; these are the loci used here. The auxiliary lemmas of the proof live in the
namespace `Proof_lem_kr3f_embedded_resolution_strong`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, pp. 137–140, 146 and Thm. 3.36(1)–(3)]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_kr3f_embedded_resolution_strong

open MMP.Resolution

/-! ### Topology -/

section Topology

variable {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']

/-- The preimage under an inducing map of an irreducible set contained in its range is
irreducible. -/
private theorem isIrreducible_preimage_of_isInducing {f : T' → T} (hf : Topology.IsInducing f)
    {s : Set T} (hs : IsIrreducible s) (hsr : s ⊆ Set.range f) : IsIrreducible (f ⁻¹' s) := by
  obtain ⟨x, hx⟩ := hs.nonempty
  obtain ⟨y, rfl⟩ := hsr hx
  refine ⟨⟨y, hx⟩, fun u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩ => ?_⟩
  obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.mp hv
  obtain ⟨z, hzs, hzu, hzv⟩ := hs.2 u' v' hu' hv' ⟨f a, ha, hau⟩ ⟨f b, hb, hbv⟩
  obtain ⟨w, rfl⟩ := hsr hzs
  exact ⟨w, hzs, hzu, hzv⟩

/-- In a noetherian space whose irreducible components are pairwise disjoint, the connected
component of a point is open and closed and is an irreducible component. -/
private theorem connectedComponent_isClopen_mem_irreducibleComponents [NoetherianSpace T]
    (hd : ∀ C ∈ irreducibleComponents T, ∀ C' ∈ irreducibleComponents T, C ≠ C' → Disjoint C C')
    (x : T) : IsClopen (connectedComponent x) ∧
      connectedComponent x ∈ irreducibleComponents T := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hxC : x ∈ C := hxC rfl
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hcompl : Cᶜ = ⋃ C' ∈ {C' ∈ irreducibleComponents T | C' ≠ C}, C' := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨C', hC', hyC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      exact ⟨C', ⟨hC', fun h ↦ hy (h ▸ hyC' rfl)⟩, hyC' rfl⟩
    · rintro ⟨C', ⟨hC', hne⟩, hyC'⟩ hyC
      exact Set.disjoint_left.mp (hd C' hC' C hC hne) hyC' hyC
  have hCop : IsOpen C := by
    rw [← isClosed_compl_iff, hcompl]
    exact ((NoetherianSpace.finite_irreducibleComponents).subset fun _ h ↦ h.1).isClosed_biUnion
      fun C' h ↦ isClosed_of_mem_irreducibleComponents C' h.1
  have hcc : connectedComponent x = C :=
    (IsClopen.connectedComponent_subset (show IsClopen C from ⟨hCcl, hCop⟩) hxC).antisymm
      ((IsPreirreducible.isPreconnected hC.1.2).subset_connectedComponent hxC)
  rw [hcc]
  exact ⟨⟨hCcl, hCop⟩, hC⟩

end Topology

/-! ### Smoothness and snc at a point -/

section Local

/-- For an open immersion `e`, `a` is a smooth point of `e ≫ s` iff `e a` is one of `s`. -/
private theorem mem_smoothLocus_comp_iff {A B S : Scheme.{u}} (e : A ⟶ B) [IsOpenImmersion e]
    (s : B ⟶ S) (a : A) : a ∈ smoothLocus (e ≫ s) ↔ e a ∈ smoothLocus s := by
  simp only [mem_smoothLocus_iff]
  constructor
  · rintro ⟨U, haU, hU⟩
    refine ⟨e ''ᵁ U, ⟨a, haU, rfl⟩, ?_⟩
    have h : (e ''ᵁ U).ι = inv (e.isoImage U).hom ≫ U.ι ≫ e := by
      rw [← Scheme.Hom.isoImage_hom_ι, IsIso.inv_hom_id_assoc]
    rw [h, Category.assoc, Category.assoc]
    infer_instance
  · rintro ⟨V, haV, hV⟩
    refine ⟨e ⁻¹ᵁ V, haV, ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

private theorem comap_comap_of_comp_eq_id {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    {g : S →+* R} (h : g.comp f = RingHom.id R) (p : PrimeSpectrum R) :
    PrimeSpectrum.comap f (PrimeSpectrum.comap g p) = p := by
  rw [← PrimeSpectrum.comap_comp_apply, h, PrimeSpectrum.comap_id]

/-- If `ψ ⁻¹' T` is snc at `y` for an open immersion `ψ`, then `T` is snc at `ψ y`. -/
private theorem isSNCAt_of_isOpenImmersion {Y Z : Scheme.{u}} (ψ : Y ⟶ Z) [IsOpenImmersion ψ]
    {T : Set Z} {y : Y} (h : IsSNCAt (ψ ⁻¹' T) y) : IsSNCAt T (ψ y) := by
  obtain ⟨n, w, C, hw, hT⟩ := h
  let φ := asIso (ψ.stalkMap y)
  refine ⟨n, fun c => φ.inv.hom (w c), C,
    isRegularSystemOfParameters_map_ringEquiv φ.symm.commRingCatIsoToRingEquiv hw, ?_⟩
  have h1 : Y.fromSpecStalk y ⁻¹' (ψ ⁻¹' T) =
      PrimeSpectrum.comap (ψ.stalkMap y).hom ⁻¹' (Z.fromSpecStalk (ψ y) ⁻¹' T) := by
    ext p
    exact Iff.of_eq (congrArg (· ∈ T) (apply_fromSpecStalk ψ y p))
  have hid : (CommRingCat.Hom.hom φ.inv).comp (ψ.stalkMap y).hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom φ.hom_inv_id
  have h2 : Z.fromSpecStalk (ψ y) ⁻¹' T = PrimeSpectrum.comap φ.inv.hom ⁻¹'
      (PrimeSpectrum.comap (ψ.stalkMap y).hom ⁻¹' (Z.fromSpecStalk (ψ y) ⁻¹' T)) := by
    ext p
    have hp : PrimeSpectrum.comap (ψ.stalkMap y).hom (PrimeSpectrum.comap φ.inv.hom p) = p :=
      comap_comap_of_comp_eq_id hid p
    exact Iff.of_eq (congrArg (fun q => Z.fromSpecStalk (ψ y) q ∈ T) hp.symm)
  rw [h2, ← h1, hT]
  simp only [Set.preimage_iUnion₂, PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]
  rfl

/-- A divisor with simple normal crossings on a smooth noetherian scheme over a field is snc at
every point. -/
private theorem isSNCAt_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of k)} [Smooth f] [NoetherianSpace Y] {D : Set Y}
    (hD : IsSNCClosedSubset f D) (y : Y) : IsSNCAt D y := by
  obtain ⟨hD, hD0 | ⟨-, -, hfam⟩⟩ := hD
  · rw [hD0]
    have := isRegularLocalRing_stalk_of_smooth_over_field f y
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
    exact ⟨n, z, ∅, hz, by simp; rfl⟩
  · exact IsSNCClosedSubset.isSNCAt_of_nonempty hD hfam y

end Local

/-! ### Blow-up sequences -/

section Sequences

open ClosedBlowupSequence

/-- The composite of a blow-up sequence of a locally noetherian scheme is proper. -/
private theorem isProper_toBase :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) [IsLocallyNoetherian X], IsProper B.toBase
  | X, .nil _, _ => (inferInstance : IsProper (𝟙 X))
  | _, .cons Z B, _ => by
    have : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    have := isProper_toBase B
    exact (inferInstance : IsProper (B.toBase ≫ blowUpToBase Z))

/-- `S.target` and `T.target` are isomorphic over the base. -/
private def OverIso {Y : Scheme.{u}} (S T : ClosedBlowupSequence Y) : Prop :=
  ∃ φ : S.target ≅ T.target, φ.hom ≫ T.toBase = S.toBase

private theorem OverIso.of_eq {Y : Scheme.{u}} {S T : ClosedBlowupSequence Y} (h : S = T) :
    OverIso S T := by
  subst h
  exact ⟨Iso.refl _, Category.id_comp _⟩

private theorem OverIso.symm {Y : Scheme.{u}} {S T : ClosedBlowupSequence Y} (h : OverIso S T) :
    OverIso T S := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.symm, by rw [← hφ, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩

private theorem OverIso.trans {Y : Scheme.{u}} {S T R : ClosedBlowupSequence Y} (h : OverIso S T)
    (h' : OverIso T R) : OverIso S R := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  exact ⟨φ ≪≫ ψ, by rw [Iso.trans_hom, Category.assoc, hψ, hφ]⟩

/-- Deleting the empty blow-ups does not change the composite. -/
private theorem overIso_reduction {Y : Scheme.{u}} (S : ClosedBlowupSequence Y) :
    OverIso S.reduction S := by
  have hP := Kollar.isPullback_pullbackReduced_toBase_of_flat S (𝟙 Y)
  have : IsIso (S.pullbackReducedHom (𝟙 Y)) := hP.isIso_snd_of_isIso
  let e := asIso (S.pullbackReducedHom (𝟙 Y))
  have hw := hP.w
  rw [Category.comp_id] at hw
  exact ⟨e, hw.symm⟩

/-- The canonical lift of the identity is the identity, up to `comap_id`. -/
private theorem canonicalLift_id_eq_eqToHom {X : Scheme.{u}} (Z : X.IdealSheafData) :
    canonicalLift (𝟙 X) Z = eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_id Z)) := by
  have key : ∀ (Z' : X.IdealSheafData) (e : Z' = Z),
      eqToHom (congrArg blowUp e) ≫ blowUpToBase Z = blowUpToBase Z' := by
    rintro _ rfl
    simp
  symm
  refine blowUpLift_unique _ _ _ _ ?_
  rw [key _ (Scheme.IdealSheafData.comap_id Z)]
  simp

private theorem pullback_eqToHom_heq {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (e : Y = X), B.pullback (eqToHom e) ≍ B := by
  induction B with
  | nil X =>
    rintro Y rfl
    rfl
  | cons Z B ih =>
    rintro Y rfl
    apply heq_of_eq
    change cons (Z.comap (eqToHom rfl)) (B.pullback (canonicalLift (eqToHom rfl) Z)) = cons Z B
    rw [cons_eq_cons_iff, eqToHom_refl, canonicalLift_id_eq_eqToHom]
    exact ⟨Scheme.IdealSheafData.comap_id Z, ih _⟩

/-- Pulling back along the identity does nothing. -/
private theorem pullback_id {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.pullback (𝟙 X) = B := by
  have := pullback_eqToHom_heq B (rfl : X = X)
  rw [eqToHom_refl] at this
  exact eq_of_heq this

/-- While every piece is active, the sequence induced on `Y` through the open `⊤` is the
pull-back. -/
private theorem embeddedAux_truncate_eq_pullback {X₀ : Scheme.{u}} (act : ℕ → X₀.Opens)
    {A' : Scheme.{u}} (C : ClosedBlowupSequence A') :
    ∀ (L n : ℕ) (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y] (p : Y ⟶ X₀) (U : Y.Opens)
      (h : U.toScheme ⟶ A') (φ : Y ⟶ A'), U = ⊤ → U.ι ≫ φ = h →
      (∀ m, 0 < m → m < L → act (n + m) = ⊤) →
      (embeddedAux act C n Y p U h).truncate L = (C.truncate L).pullback φ := by
  induction C with
  | nil _ => intro L n Y _ p U h φ _ _ _; cases L <;> rfl
  | cons Z C ih =>
    intro L n Y _ p U h φ hU hh hact
    subst hU hh
    rw [Kollar.embeddedAux_cons]
    cases L with
    | zero => rfl
    | succ L =>
      have : IsIso (⊤ : Y.Opens).ι := Y.topIso_hom ▸ inferInstance
      have hW : (Z.comap ((⊤ : Y.Opens).ι ≫ φ)).map (⊤ : Y.Opens).ι = Z.comap φ := by
        have e1 := Kollar.comap_eq_map_inv (inv (⊤ : Y.Opens).ι)
          ((Z.comap φ).comap (⊤ : Y.Opens).ι)
        rw [IsIso.inv_inv] at e1
        rw [Scheme.IdealSheafData.comap_comp, ← e1, Kollar.comap_comap_inv]
      change cons _ _ = cons (Z.comap φ) ((C.truncate L).pullback (canonicalLift φ Z))
      rw [cons_eq_cons_iff]
      refine ⟨hW, ?_⟩
      rcases Nat.eq_zero_or_pos L with rfl | hL
      · rw [Kollar.truncate_zero, Kollar.truncate_zero]
        exact congr_arg_heq ClosedBlowupSequence.nil (congrArg blowUp hW)
      · have := Kollar.isNoetherian_blowUp' ((Z.comap ((⊤ : Y.Opens).ι ≫ φ)).map (⊤ : Y.Opens).ι)
        refine HEq.trans (heq_of_eq (ih L (n + 1) _ _ _ _
          (eqToHom (congrArg blowUp hW) ≫ canonicalLift φ Z) ?_ ?_ ?_))
          (pullback_eqToHom_comp_heq _ _ _)
        · rw [hact 1 one_pos (by omega)]
          simp
        · apply blowUpLift_unique
          rw [Category.assoc, Category.assoc, canonicalLift_comp_blowUpToBase,
            ← Category.assoc (eqToHom _), Kollar.eqToHom_blowUpToBase hW,
            Scheme.Hom.resLE_comp_ι_assoc]
        · intro m hm hmL
          rw [show n + 1 + m = n + (m + 1) by omega]
          exact hact _ (by omega) (by omega)

/-- On a connected scheme with a generic point `η`, the induced sequence `𝓑𝓡_𝐁(U ⊆ A)` is the
pull-back of `𝐁` truncated at the entry index of `η`. -/
private theorem embeddedResolutionSequence_eq_pullback_truncate {U A : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian U] (B : ClosedBlowupSequence A) (i' : U ⟶ A) (η : U)
    (hcc : ∀ y : U, connectedComponent y = Set.univ) (hη : closure {η} = Set.univ) :
    embeddedResolutionSequence B i' = (B.truncate (B.entryIndex (i' η))).pullback i' := by
  have hgen : ∀ η' : U, connectedComponent η' ⊆ closure {η'} → η' = η := fun η' h' =>
    (show IsGenericPoint η' Set.univ from Set.eq_univ_of_univ_subset (hcc η' ▸ h')).eq hη
  set j := B.entryIndex (i' η)
  have hcomp : ∀ x, componentEntryIndex B i' x = j := by
    intro x
    unfold componentEntryIndex
    have hex : ∃ η' ∈ connectedComponent x, connectedComponent x ⊆ closure {η'} :=
      ⟨η, by rw [hcc x]; trivial, by rw [hcc x, hη]⟩
    rw [dite_eq_left hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [hgen hex.choose (by rw [← connectedComponent_eq h1]; exact h2)]
  have hact : ∀ n, activeLocus B i' n = if n < j then ⊤ else ⊥ := by
    intro n
    have hset : {x : U | n < componentEntryIndex B i' x} = if n < j then Set.univ else ∅ := by
      ext x
      rw [Set.mem_ofPred_eq, hcomp]
      split_ifs with hn
      · simpa only [Set.mem_univ, iff_true] using hn
      · simpa only [Set.mem_empty_iff_false, iff_false] using hn
    have hop : IsOpen {x : U | n < componentEntryIndex B i' x} := by
      rw [hset]
      split_ifs
      · exact isOpen_univ
      · exact isOpen_empty
    unfold activeLocus
    rw [dite_eq_left hop]
    split_ifs with hn <;> ext x <;> simp [hcomp, hn]
  have hlen : embeddedResolutionLength B i' = j := by
    unfold embeddedResolutionLength
    have : {j' | ∃ η' : U, connectedComponent η' ⊆ closure {η'} ∧
        j' = B.entryIndex (i' η')} = {j} := by
      ext j'
      constructor
      · rintro ⟨η', h1, rfl⟩
        rw [hgen η' h1]
        rfl
      · rintro rfl
        exact ⟨η, by rw [hcc η, hη], rfl⟩
    rw [this, csSup_singleton]
  unfold embeddedResolutionSequence
  rw [hlen]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, Kollar.truncate_zero, Kollar.truncate_zero]
    rfl
  · exact embeddedAux_truncate_eq_pullback _ B j 0 U (𝟙 U) _ _ i' (by rw [hact, ite_eq_left hj0])
      rfl (fun m _ hm => by rw [hact, ite_eq_left (by omega)])

/-- The pull-back along an isomorphism `e` has the same last scheme, over `e`. -/
private theorem exists_iso_pullback_target {Y Z : Scheme.{u}} (T : ClosedBlowupSequence Z)
    (e : Y ≅ Z) : ∃ φ : (T.pullback e.hom).target ≅ T.target,
      φ.hom ≫ T.toBase = (T.pullback e.hom).toBase ≫ e.hom := by
  have hP := Kollar.isPullback_pullback_toBase_of_flat T e.hom
  have := hP.isIso_snd_of_isIso
  exact ⟨asIso (T.pullbackHom e.hom), hP.w.symm⟩

/-- The preimage of an open `U` under the composite `R.toBase` is the last scheme of the
pull-back to `U`, over `U`. -/
private theorem exists_iso_preimage_of_overIso {X : Scheme.{u}} (R : ClosedBlowupSequence X)
    (U : X.Opens) (Q : ClosedBlowupSequence U.toScheme) (hQ : OverIso (R.pullback U.ι) Q) :
    ∃ φ : (R.toBase ⁻¹ᵁ U).toScheme ≅ Q.target, φ.hom ≫ Q.toBase = R.toBase ∣_ U := by
  obtain ⟨ψ, hψ⟩ := hQ
  have sq1 := isPullback_morphismRestrict R.toBase U
  have sq2 := Kollar.isPullback_pullback_toBase_of_flat R U.ι
  refine ⟨sq1.isoIsPullback _ _ sq2 ≪≫ ψ, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hψ, IsPullback.isoIsPullback_hom_fst]

end Sequences

/-! ### Disjoint unions of varieties -/

section Components

private theorem isNoetherian_of_isDisjointUnionOfVarieties {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties s) :
    AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨_, _, -⟩ := hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  exact {}

private theorem subschemeι_eqToHom {Y : Scheme.{u}} {I J : Y.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp

/-- The ideal sheaf of a quasi-compact morphism from a reduced scheme is the vanishing ideal of
the closure of its image. -/
private theorem ker_eq_vanishingIdeal {X Y : Scheme.{u}} (f : Y ⟶ X) [IsReduced Y]
    [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
  rw [← Set.image_univ, ← Scheme.IdealSheafData.map_bot]
  have := Scheme.IdealSheafData.map_vanishingIdeal f ⊤
  rwa [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at this

variable {k : Type u} [Field k] {X A : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}

/-- The support of the ideal of `X` is the image of `X`. -/
private theorem coe_support_ker [IsClosedImmersion i] :
    (i.ker.support : Set A) = Set.range i := by
  rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]

/-- For an admissible embedding every irreducible closed subset of `X` has codimension `≥ 2` in
`A`. -/
private theorem two_le_closedsCodimension_support_ker (h : IsAdmissibleEmbedding sA i) :
    2 ≤ closedsCodimension i.ker.support := by
  have : IsClosedImmersion i := h.2.2.2.1
  rw [le_closedsCodimension_iff]
  intro W hW
  rw [coe_support_ker] at hW
  have hW₀ : IsIrreducible (i.base ⁻¹' (W : Set A)) :=
    isIrreducible_preimage_of_isInducing i.isClosedEmbedding.isInducing W.isIrreducible hW
  obtain ⟨C, hC, hW₀C⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hW₀
  obtain ⟨T, hT, hCT⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hC.1.image i.base i.base.hom.continuous.continuousOn)
  obtain ⟨Y₁, Y₂, h1, h2, -⟩ := h.2.2.2.2.2.2.2 C hC T hT hCT
  have hWC : (W : Set A) ⊆ i.base '' C := fun a ha => by
    obtain ⟨x, rfl⟩ := hW ha
    exact ⟨x, hW₀C ha, rfl⟩
  have hWY : W < Y₁ := SetLike.coe_ssubset_coe.mp (hWC.trans_ssubset h1)
  have hY : Y₁ < Y₂ := SetLike.coe_ssubset_coe.mp h2
  have := (codimension_iff_exists_chain W 2).2
    ⟨⟨2, ![W, Y₁, Y₂], fun j => by fin_cases j <;> simpa⟩, rfl, rfl⟩
  exact_mod_cast this

/-- The closed subscheme `X` of `A` is reduced. -/
private theorem isReduced_subscheme_ker (h : IsAdmissibleEmbedding sA i) :
    IsReduced i.ker.subscheme := by
  have : IsClosedImmersion i := h.2.2.2.1
  have : IsReduced X := h.2.2.1.2.2.1
  exact isReduced_of_isOpenImmersion (inv (Scheme.Hom.toImage i))

private theorem closure_singleton_image_eq [IsClosedImmersion i] {U : Set X} {η : X}
    (hηU : closure {η} = U) : closure {i η} = i '' U := by
  rw [← hηU, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton]

/-- For `U` an irreducible component of `X` with generic point `η`, `closure {i η}` is an
irreducible component of the support of `I_X`. -/
private theorem closure_mem_componentsOf [IsClosedImmersion i] {U : Set X}
    (hU : U ∈ irreducibleComponents X) {η : X} (hηU : closure {η} = U) :
    closure {i η} ∈ componentsOf (i.ker.support : Set A) := by
  have himg : closure {i η} = i '' U := closure_singleton_image_eq hηU
  rw [coe_support_ker]
  refine ⟨⟨isIrreducible_singleton.closure, himg ▸ Set.image_subset_range _ _⟩,
    fun s ⟨hs, hsr⟩ hle => ?_⟩
  have hs₀ := isIrreducible_preimage_of_isInducing i.isClosedEmbedding.isInducing hs hsr
  have hUs : U ⊆ i.base ⁻¹' s := fun x hx => hle (himg ▸ ⟨x, hx, rfl⟩)
  have := hU.2 ⟨hs₀.nonempty, hs₀.2⟩ hUs
  rw [himg]
  intro a ha
  obtain ⟨x, rfl⟩ := hsr ha
  exact ⟨x, this ha, rfl⟩

/-- A component `U` of `X` which is open and closed meets no other component of the support of
`I_X`. -/
private theorem disjoint_of_isClopen [IsClosedImmersion i] {U : Set X}
    (hU : U ∈ irreducibleComponents X) (hUcl : IsClopen U) {η : X} (hηU : closure {η} = U) :
    ∀ Z ∈ componentsOf (i.ker.support : Set A), Z ≠ closure {i η} →
      Disjoint Z (closure {i η}) := by
  have himg : closure {i η} = i '' U := closure_singleton_image_eq hηU
  have hmem := closure_mem_componentsOf (i := i) hU hηU
  rw [coe_support_ker] at hmem ⊢
  intro Z hZ hne
  rw [Set.disjoint_iff]
  rintro a ⟨haZ, haC⟩
  apply hne
  have hZ₀ := isIrreducible_preimage_of_isInducing i.isClosedEmbedding.isInducing hZ.1.1 hZ.1.2
  rw [himg] at haC
  obtain ⟨x, hxU, rfl⟩ := haC
  have hsub : i.base ⁻¹' Z ⊆ U := hZ₀.2.isPreconnected.subset_isClopen hUcl ⟨x, haZ, hxU⟩
  have hZC : Z ⊆ closure {i η} := by
    rw [himg]
    intro b hb
    obtain ⟨y, rfl⟩ := hZ.1.2 hb
    exact ⟨y, hsub hb, rfl⟩
  exact le_antisymm hZC (hZ.2 hmem.1 hZC)

/-! ### The induced sequence over a connected component -/

/-- The ideal of an open subscheme `U` of `X` with generic point `η`, closed in `A`, is the
vanishing ideal of `closure {i η}`. -/
private theorem ker_ι_comp_eq_vanishingIdeal [IsClosedImmersion i] (U : X.Opens)
    [IsReduced U.toScheme] [QuasiCompact U.ι] {η : X} (hηU : closure {η} = (U : Set X)) :
    (U.ι ≫ i).ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure {i η}, isClosed_closure⟩ := by
  rw [ker_eq_vanishingIdeal (U.ι ≫ i)]
  congr 1
  ext1
  change closure (Set.range (U.ι ≫ i)) = closure {i η}
  have hr : Set.range (U.ι ≫ i) = i.base '' (U : Set X) := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨U.ι y, y.2, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι := by
        rw [Scheme.Opens.range_ι]
        exact hx
      exact ⟨y, by rw [Scheme.Hom.comp_apply]⟩
  rw [hr, ← hηU, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, closure_closure]

/-- Over an open and closed irreducible component `U` of `X` with generic point `η`, the
preimage of `U` in `X_r` is the last scheme `C_j` of the restriction to `C = closure {i η}` of
the first `j = j_𝐁(i η)` steps of `𝐁 = 𝓑𝓟^can(A, I_X, ∅)`, compatibly with the maps to `A`. -/
private theorem exists_iso_preimage_component (h : IsAdmissibleEmbedding sA i) (U : X.Opens)
    (hUcl : IsClopen (U : Set X)) (hU : (U : Set X) ∈ irreducibleComponents X) (η : X)
    (hηU : closure {η} = (U : Set X)) :
    let B : ClosedBlowupSequence A :=
      canonicalPrincipalization (embeddingTriple sA i) (embeddingTriple_mem_sncTriples h)
    let C : A.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {i η}, isClosed_closure⟩
    let T := (B.truncate (B.entryIndex (i η))).restrict C
    ∃ (e : U.toScheme ≅ C.subscheme)
      (Ψ : ((embeddedResolution sA i).toBase ⁻¹ᵁ U).toScheme ≅ T.target),
      e.hom ≫ C.subschemeι = U.ι ≫ i ∧
        Ψ.hom ≫ T.toBase = ((embeddedResolution sA i).toBase ∣_ U) ≫ e.hom := by
  intro B C T
  have : IsClosedImmersion i := h.2.2.2.1
  have hXdu := h.2.2.1
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isDisjointUnionOfVarieties hXdu
  have : IsReduced X := hXdu.2.2.1
  have : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  have : QuasiCompact sA := (embeddingTriple_mem_sncTriples h).2.2.2.1
  have hηmem : η ∈ (U : Set X) := hηU ▸ subset_closure rfl
  let ηU : U.toScheme := ⟨η, hηmem⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set X)
  have : AlgebraicGeometry.IsNoetherian U.toScheme := {}
  have hirrU : IrreducibleSpace U.toScheme :=
    (isIrreducible_iff_irreducibleSpace (s := (U : Set X))).mp hU.1
  have hcc : ∀ y : U.toScheme, connectedComponent y = Set.univ := fun y =>
    PreconnectedSpace.connectedComponent_eq_univ y
  have hηU' : closure {ηU} = Set.univ := by
    rw [U.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      show U.ι.base ηU = η from rfl, hηU]
    exact Set.eq_univ_of_forall fun y => y.2
  let f := U.ι ≫ i
  have : IsClosedImmersion U.ι := IsClosedImmersion.iff_isPreimmersion.mpr
    ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hUcl.isClosed⟩
  have hker : f.ker = C := ker_ι_comp_eq_vanishingIdeal U hηU
  let e : U.toScheme ≅ C.subscheme :=
    asIso f.toImage ≪≫ eqToIso (show f.ker.subscheme = C.subscheme by rw [hker])
  have he : e.hom ≫ C.subschemeι = U.ι ≫ i := by
    have : e.hom = f.toImage ≫ eqToHom (show f.ker.subscheme = C.subscheme by rw [hker]) := rfl
    rw [this, Category.assoc, subschemeι_eqToHom hker]
    exact f.toImage_imageι
  refine ⟨e, ?_⟩
  set S := embeddedResolutionSequence B i
  have hR : embeddedResolution sA i = S.reduction := dite_eq_left (embeddingTriple_mem_sncTriples h)
  have hXU : IsDisjointUnionOfVarieties (f ≫ sA) := by
    have : IsSeparated (i ≫ sA) := hXdu.2.2.2.1
    refine ⟨inferInstance, inferInstance, inferInstance,
      by
        change IsSeparated (U.ι ≫ (i ≫ sA))
        infer_instance, ?_⟩
    intro C₁ hC₁ C₂ hC₂ hne
    rw [irreducibleComponents_eq_singleton] at hC₁ hC₂
    exact absurd (hC₁.trans hC₂.symm) hne
  have hred : ((S.pullback U.ι).reduction) = (embeddedResolutionSequence B f).reduction := by
    rw [← Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm sA i hXdu B sA
      (𝟙 A) U.ι f (Category.comp_id _) hXU, pullback_id]
  have hconn := embeddedResolutionSequence_eq_pullback_truncate B f ηU hcc hηU'
  have hpb : (B.truncate (B.entryIndex (i η))).pullback f = T.pullback e.hom :=
    (eq_of_heq (ClosedBlowupSequence.pullback_pullback_heq _ C.subschemeι e.hom f rfl
      (by rw [eqToHom_refl, Category.id_comp, he]))).symm
  have hQ : OverIso ((embeddedResolution sA i).pullback U.ι) (T.pullback e.hom) := by
    rw [hR]
    refine (overIso_reduction _).symm.trans ?_
    rw [ClosedBlowupSequence.reduction_pullback_reduction, hred]
    refine (overIso_reduction _).trans (OverIso.of_eq ?_)
    rw [hconn, ← hpb]
    rfl
  obtain ⟨φ₁, hφ₁⟩ := exists_iso_preimage_of_overIso _ U _ hQ
  obtain ⟨φ₂, hφ₂⟩ := exists_iso_pullback_target T e
  refine ⟨φ₁ ≪≫ φ₂, he, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hφ₂, ← Category.assoc, hφ₁]

end Components

/-! ### The restricted sequence is smooth -/

section Smooth

/-- If the concatenation `D.append E` of blow-up sequences is smooth over `k`, so is `E`, over
the composite `D.toBase ≫ s`. -/
private theorem isSmooth_of_isSmooth_append {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (D : ClosedBlowupSequence X) (E : ClosedBlowupSequence D.target)
    (h : (D.append E).IsSmooth s) : E.IsSmooth (D.toBase ≫ s) := by
  induction D with
  | nil X =>
    change E.IsSmooth (𝟙 X ≫ s)
    rwa [Category.id_comp]
  | cons Z D ih =>
    change E.IsSmooth ((D.toBase ≫ blowUpToBase Z) ≫ s)
    rw [Category.assoc]
    exact ih _ E h.2.2

/-- A closed subscheme `W` whose ideal agrees, on an open `U` containing its support, with the
ideal of a closed subscheme `Z` smooth over `T`, is itself smooth over `T`. -/
private theorem smooth_subschemeι_of_comap_eq {Y T : Scheme.{u}} (t : Y ⟶ T)
    (W Z : Y.IdealSheafData) (U : Y.Opens) (hWU : (W.support : Set Y) ⊆ U)
    (h : W.comap U.ι = Z.comap U.ι) (hZ : Smooth (Z.subschemeι ≫ t)) :
    Smooth (W.subschemeι ≫ t) := by
  have key : ∀ V : U.toScheme.IdealSheafData, V = Z.comap U.ι →
      Smooth (V.subschemeι ≫ U.ι ≫ t) := by
    rintro _ rfl
    have e : (Z.comap U.ι).subschemeι ≫ U.ι ≫ t =
        ((Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι) ≫ Z.subschemeι ≫ t := by
      rw [← Z.comapIso_hom_fst U.ι, Category.assoc, Category.assoc, ← Category.assoc _ U.ι,
        Limits.pullback.condition, Category.assoc]
    rw [e]
    infer_instance
  have hW := key _ h
  have hsnd : IsIso (Limits.pullback.snd U.ι W.subschemeι) := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : W.subschemeι x ∈ U := hWU (by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
    change x ∈ Set.range (Limits.pullback.snd U.ι W.subschemeι)
    rw [IsOpenImmersion.range_pullbackSnd]
    simpa using hx
  have e : W.subschemeι ≫ t = inv (Limits.pullback.snd U.ι W.subschemeι) ≫
      ((W.comapIso U.ι).inv ≫ (W.comap U.ι).subschemeι ≫ U.ι ≫ t) := by
    rw [← W.comapIso_hom_fst U.ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Limits.pullback.condition_assoc, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- If the closed subscheme `T.restrictHom C` of `T.target` agrees, on an open `U` containing
it, with a closed subscheme `Z` smooth over `T.toBase ≫ t`, then the restricted composite is
smooth over `t`. -/
private theorem smooth_restrict_toBase_comp {X S : Scheme.{u}} (t : X ⟶ S)
    (T : ClosedBlowupSequence X) (C : X.IdealSheafData) [IsClosedImmersion (T.restrictHom C)]
    (Z : T.target.IdealSheafData) (U : T.target.Opens)
    (hιU : Set.range (T.restrictHom C) ⊆ U)
    (hker : (T.restrictHom C).ker.comap U.ι = Z.comap U.ι)
    (hZ : Smooth (Z.subschemeι ≫ T.toBase ≫ t)) :
    Smooth ((T.restrict C).toBase ≫ C.subschemeι ≫ t) := by
  have hW := smooth_subschemeι_of_comap_eq _ _ Z U (by
    rwa [Scheme.Hom.support_ker, (T.restrictHom C).isClosedEmbedding.isClosed_range.closure_eq])
    hker hZ
  have hc : (T.restrict C).toBase ≫ C.subschemeι = T.restrictHom C ≫ T.toBase :=
    (Kollar.pullbackHom_toBase_comm _ _).symm
  rw [← Category.assoc, hc, ← Scheme.Hom.toImage_imageι (T.restrictHom C)]
  simp only [Category.assoc]
  infer_instance

/-- The last scheme of a blow-up sequence of a locally noetherian scheme is locally noetherian. -/
private theorem isLocallyNoetherian_target :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) [IsLocallyNoetherian X],
      IsLocallyNoetherian B.target
  | _, .nil _, _ => ‹_›
  | _, .cons Z B, _ =>
    have : IsLocallyNoetherian (blowUp Z) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
    isLocallyNoetherian_target B

/-- Codimension `≥ 2` of a closed set `S` containing `closure {η}` gives a chain
`closure {η} ⊂ Y₁ ⊂ Y₂` of irreducible closed subsets. -/
private theorem exists_ssubset_ssubset_of_two_le_closedsCodimension {T : Type*}
    [TopologicalSpace T] {S : Closeds T} (hS : 2 ≤ closedsCodimension S) {η : T}
    (hη : closure {η} ⊆ (S : Set T)) :
    ∃ Y₁ Y₂ : IrreducibleCloseds T, closure {η} ⊂ (Y₁ : Set T) ∧ (Y₁ : Set T) ⊂ Y₂ := by
  let Y : IrreducibleCloseds T := ⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨p, hhead, hlen⟩ := (codimension_iff_exists_chain Y 2).1
    (by simpa using le_closedsCodimension_iff.mp hS Y hη)
  refine ⟨p ⟨1, by omega⟩, p ⟨2, by omega⟩, ?_, p.strictMono (by simp [Fin.lt_def])⟩
  change Y < p ⟨1, by omega⟩
  rw [← hhead]
  exact p.strictMono (by simp [Fin.lt_def])

variable {k : Type u} [Field k] {X A : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}

/-- For an admissible embedding the triple `(A, I_X, ∅)` lies in the domain of `𝓑𝓟^can`. -/
private theorem embeddingTriple_mem_triples (h : IsAdmissibleEmbedding sA i) :
    embeddingTriple sA i ∈ triples := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := embeddingTriple_mem_sncTriples h
  exact ⟨h0, h1, h2, h3, h.2.2.2.2.2.2.1, h4, h5, h6⟩

/-- **`C_j` is smooth** (Kollár p. 137): the restriction to an irreducible component `C` of `X`
of the first `j = j_𝐁(η_C)` steps of `𝐁 = 𝓑𝓟^can(A, I_X, ∅)` ends in a scheme smooth over `k`,
an open and closed piece of the smooth centre `Z_j`. -/
private theorem smooth_toBase_restrict_truncate_entryIndex (h : IsAdmissibleEmbedding sA i)
    (η : A) (hη : closure {η} ∈ componentsOf (i.ker.support : Set A)) :
    let B : ClosedBlowupSequence A :=
      canonicalPrincipalization (embeddingTriple sA i) (embeddingTriple_mem_sncTriples h)
    let C : A.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩
    Smooth (((B.truncate (B.entryIndex η)).restrict C).toBase ≫ C.subschemeι ≫ sA) := by
  intro B C
  have ht := embeddingTriple_mem_triples h
  have hsm : IsSmoothScheme sA := h.2.2.2.2.2.1
  have : Smooth sA := IsSmoothScheme.smooth hsm
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have hηmax : Maximal (fun s : Set A => IsIrreducible s ∧ s ⊆ (i.ker.support : Set A))
      (closure {η}) := hη
  obtain ⟨h1, h2, h3, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  have hBsm : B.IsSmooth sA := (h1 _ ht).1
  have hcent : B.CentersLieOver (𝟙 A) (i.ker.support : Set A) := (h3 _ ht (by
    intro W hW
    obtain ⟨x, hx⟩ := hW.1.1.nonempty
    obtain ⟨j, -⟩ := Set.mem_iUnion.1 (hW.1.2 hx)
    exact j.elim0)).1
  have : IsLocallyNoetherian B.target := isLocallyNoetherian_target B
  have hprinc : Stacks.Divisors.IsLocallyPrincipal (i.ker.comap B.toBase) := by
    refine Stacks.Divisors.isLocallyPrincipal_of_stalk_isPrincipal _ fun x _ => ?_
    obtain ⟨n, z, c, -, hx⟩ := h2 _ ht x
    exact ⟨_, hx⟩
  obtain ⟨-, Z, B', hBeq, -, U, hιU, hker⟩ :=
    ClosedBlowupSequence.restrict_truncate_entryIndex_isConnectedComponent sA hsm i.ker hηmax
      (exists_ssubset_ssubset_of_two_le_closedsCodimension
        (two_le_closedsCodimension_support_ker h) hηmax.prop.2) B hBsm hprinc hcent
  have hB' : ((B.truncate (B.entryIndex η)).append (.cons Z B')).IsSmooth sA := hBeq ▸ hBsm
  have := Kollar.isClosedImmersion_restrictHom_truncate B C (B.entryIndex η)
  exact smooth_restrict_toBase_comp sA _ C Z U hιU hker
    (IsSmoothScheme.smooth (isSmooth_of_isSmooth_append sA _ _ hB').2.1)

end Smooth

/-! ### The data attached to a component -/

section Data

variable {k : Type u} [Field k] {X A : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}

/-- A smooth point of `X` gives a smooth point of the closed subscheme `V(I_X)` of `A`. -/
private theorem toImage_mem_smoothLocus [IsClosedImmersion i] {x : X}
    (hx : x ∈ smoothLocus (i ≫ sA)) : i.toImage x ∈ smoothLocus (i.ker.subschemeι ≫ sA) :=
  (mem_smoothLocus_comp_iff i.toImage (i.ker.subschemeι ≫ sA) x).1
    (by rwa [← Category.assoc, Scheme.Hom.toImage_imageι])

private theorem subschemeι_toImage (x : X) :
    i.ker.subschemeι (i.toImage x) = i x := by
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

/-- Everything the proof uses about one open and closed component `U` of `X`: with
`C = closure {i η}`, `T` the restriction to `C` of the first `j_𝐁(i η)` steps of `𝐁`, `Π⁻¹(U)`
is the last scheme of `T` over `U ≅ C`; this scheme is smooth; the preimage of `Sing C` in it is
the trace of the total exceptional set, a divisor with simple normal crossings; and the
composite of `T` is an isomorphism near every smooth point of `X` on `U`. -/
private theorem exists_component_data (h : IsAdmissibleEmbedding sA i) (U : X.Opens)
    (hUcl : IsClopen (U : Set X)) (hU : (U : Set X) ∈ irreducibleComponents X) (η : X)
    (hηU : closure {η} = (U : Set X)) :
    ∃ (B : ClosedBlowupSequence A) (C : A.IdealSheafData) (e : U.toScheme ≅ C.subscheme)
      (Ψ : ((embeddedResolution sA i).toBase ⁻¹ᵁ U).toScheme ≅
        ((B.truncate (B.entryIndex (i η))).restrict C).target),
      e.hom ≫ C.subschemeι = U.ι ≫ i ∧
      Ψ.hom ≫ ((B.truncate (B.entryIndex (i η))).restrict C).toBase =
        ((embeddedResolution sA i).toBase ∣_ U) ≫ e.hom ∧
      Smooth (((B.truncate (B.entryIndex (i η))).restrict C).toBase ≫ C.subschemeι ≫ sA) ∧
      ((B.truncate (B.entryIndex (i η))).restrict C).toBase.base ⁻¹'
          (singularLocus (C.subschemeι ≫ sA) : Set C.subscheme) =
        ((B.truncate (B.entryIndex (i η))).restrictHom C).base ⁻¹'
          (B.truncate (B.entryIndex (i η))).totalExceptionalSet ∧
      IsSNCClosedSubset
        (((B.truncate (B.entryIndex (i η))).restrict C).toBase ≫ C.subschemeι ≫ sA)
        ((B.truncate (B.entryIndex (i η))).restrictHom C ⁻¹'
          (B.truncate (B.entryIndex (i η))).totalExceptionalSet) ∧
      ∀ x : U.toScheme, U.ι x ∈ smoothLocus (i ≫ sA) →
        ∃ V : C.subscheme.Opens, e.hom x ∈ V ∧
          IsIso (((B.truncate (B.entryIndex (i η))).restrict C).toBase ∣_ V) := by
  have hchar : CharZero k := h.1
  have : IsClosedImmersion i := h.2.2.2.1
  have : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  have : QuasiCompact sA := (embeddingTriple_mem_sncTriples h).2.2.2.1
  have hsm : IsSmoothScheme sA := h.2.2.2.2.2.1
  have heq : Equidimensional A := h.2.2.2.2.2.2.1
  have hred := isReduced_subscheme_ker h
  have hcodim := two_le_closedsCodimension_support_ker h
  have hηmax := closure_mem_componentsOf (i := i) hU hηU
  have himg : closure {i η} = i '' U := closure_singleton_image_eq hηU
  have hxC : ∀ x ∈ (U : Set X), i.ker.subschemeι (i.toImage x) ∈ closure {i η} := fun x hx => by
    rw [subschemeι_toImage, himg]
    exact ⟨x, hx, rfl⟩
  let C : A.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨closure {i η}, isClosed_closure⟩
  obtain ⟨e, Ψ, he, hΨ⟩ := exists_iso_preimage_component h U hUcl hU η hηU
  have hCj := smooth_toBase_restrict_truncate_entryIndex h (i η) hηmax
  obtain ⟨_, hsing⟩ := preimage_singularLocus_toBase_restrict_canonicalPrincipalization sA hsm
    heq i.ker hred hcodim (i η) hηmax (disjoint_of_isClopen hU hUcl hηU)
  obtain ⟨x₀, hx₀U, hx₀⟩ : ∃ x₀ ∈ (U : Set X), x₀ ∈ smoothLocus (i ≫ sA) := by
    have : IsReduced X := h.2.2.1.2.2.1
    have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
    have : IrreducibleSpace U.toScheme :=
      (isIrreducible_iff_irreducibleSpace (s := (U : Set X))).mp hU.1
    have : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ i ≫ sA)
    have := MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (k := k)
      (X := U.toScheme) (f := U.ι ≫ i ≫ sA)
    exact ⟨U.ι (genericPoint U), (genericPoint U).2,
      (mem_smoothLocus_comp_iff U.ι (i ≫ sA) _).1 this⟩
  obtain ⟨_, hsnc⟩ :=
    isSNCClosedSubset_restrictHom_preimage_totalExceptionalSet_canonicalPrincipalization
      sA hsm heq i.ker hcodim (i η) hηmax (i.toImage x₀) (toImage_mem_smoothLocus hx₀)
      (hxC x₀ hx₀U)
  refine ⟨canonicalPrincipalization (embeddingTriple sA i) (embeddingTriple_mem_sncTriples h), C,
    e, Ψ, he, hΨ, hCj, hsing, hsnc, fun x hxs => ?_⟩
  obtain ⟨_, V, y, hy, hyV, hiso⟩ :=
    exists_isIso_morphismRestrict_toBase_restrict_canonicalPrincipalization sA hsm heq i.ker
      hcodim (i η) hηmax (i.toImage (U.ι x)) (toImage_mem_smoothLocus hxs) (hxC _ x.2)
  refine ⟨V, ?_, hiso⟩
  have hey : e.hom x = y := by
    apply C.subschemeι.isClosedEmbedding.injective
    have h1 : C.subschemeι (e.hom x) = i (U.ι x) := by
      rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    rw [h1, hy, subschemeι_toImage]
  rw [hey]
  exact hyV

/-- Every point of `X` lies on an open and closed irreducible component of `X`, which has a
generic point. -/
private theorem exists_clopen_component (h : IsAdmissibleEmbedding sA i) (x : X) :
    ∃ (U : X.Opens) (η : X), x ∈ U ∧ IsClopen (U : Set X) ∧
      (U : Set X) ∈ irreducibleComponents X ∧ closure {η} = (U : Set X) := by
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isDisjointUnionOfVarieties h.2.2.1
  obtain ⟨hcl, hirr⟩ := connectedComponent_isClopen_mem_irreducibleComponents h.2.2.1.2.2.2.2 x
  obtain ⟨η, hη⟩ := QuasiSober.sober hirr.1 hcl.isClosed
  exact ⟨⟨_, hcl.isOpen⟩, η, mem_connectedComponent, hcl, hirr, hη⟩

/-- Over a component `U`, the structure map of `Π⁻¹(U)` factors as `Ψ` followed by the
structure map of `C_j`. -/
private theorem ι_comp_toBase_eq {U : X.Opens} {C : A.IdealSheafData}
    {T : ClosedBlowupSequence C.subscheme} {e : U.toScheme ≅ C.subscheme}
    {Ψ : ((embeddedResolution sA i).toBase ⁻¹ᵁ U).toScheme ≅ T.target}
    (he : e.hom ≫ C.subschemeι = U.ι ≫ i)
    (hΨ : Ψ.hom ≫ T.toBase = ((embeddedResolution sA i).toBase ∣_ U) ≫ e.hom) :
    ((embeddedResolution sA i).toBase ⁻¹ᵁ U).ι ≫ (embeddedResolution sA i).toBase ≫ i ≫ sA =
      Ψ.hom ≫ T.toBase ≫ C.subschemeι ≫ sA := by
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc, ← reassoc_of% he,
    ← reassoc_of% hΨ]

/-- Over a component `U`, `Ψ` carries `Π⁻¹(Sing X) ∩ Π⁻¹(U)` onto the preimage of `Sing C` in
`C_j`. -/
private theorem preimage_preimage_singularLocus {U : X.Opens}
    {C : A.IdealSheafData} {T : ClosedBlowupSequence C.subscheme} {e : U.toScheme ≅ C.subscheme}
    {Ψ : ((embeddedResolution sA i).toBase ⁻¹ᵁ U).toScheme ≅ T.target}
    (he : e.hom ≫ C.subschemeι = U.ι ≫ i)
    (hΨ : Ψ.hom ≫ T.toBase = ((embeddedResolution sA i).toBase ∣_ U) ≫ e.hom) :
    Ψ.hom ⁻¹' (T.toBase ⁻¹' (singularLocus (C.subschemeι ≫ sA) : Set C.subscheme)) =
      ((embeddedResolution sA i).toBase ⁻¹ᵁ U).ι ⁻¹'
        ((embeddedResolution sA i).toBase ⁻¹' (singularLocus (i ≫ sA) : Set X)) := by
  ext w
  simp only [Set.mem_preimage]
  have hw1 : T.toBase (Ψ.hom w) = e.hom (((embeddedResolution sA i).toBase ∣_ U) w) := by
    rw [← Scheme.Hom.comp_apply, hΨ, Scheme.Hom.comp_apply]
  have hw2 : (embeddedResolution sA i).toBase (((embeddedResolution sA i).toBase ⁻¹ᵁ U).ι w) =
      U.ι (((embeddedResolution sA i).toBase ∣_ U) w) := by
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  rw [hw1, hw2, SetLike.mem_coe, SetLike.mem_coe, mem_singularLocus_iff,
    mem_singularLocus_iff, not_iff_not, ← mem_smoothLocus_comp_iff e.hom,
    ← mem_smoothLocus_comp_iff U.ι, reassoc_of% he]

/-- **`X_r` is smooth**, at each point: over a component `U`, `Π⁻¹(U) ≅ C_j` is smooth. -/
private theorem mem_smoothLocus_toBase (h : IsAdmissibleEmbedding sA i)
    (y : (embeddedResolution sA i).target) :
    y ∈ smoothLocus ((embeddedResolution sA i).toBase ≫ i ≫ sA) := by
  obtain ⟨U, η, hyU, hUcl, hU, hηU⟩ :=
    exists_clopen_component h ((embeddedResolution sA i).toBase y)
  obtain ⟨B, C, e, Ψ, he, hΨ, hCj, -⟩ := exists_component_data h U hUcl hU η hηU
  refine mem_smoothLocus_iff.2 ⟨(embeddedResolution sA i).toBase ⁻¹ᵁ U, hyU, ?_⟩
  rw [ι_comp_toBase_eq he hΨ]
  exact MorphismProperty.comp_mem @Smooth _ _ inferInstance hCj

/-- **`Π` is an isomorphism near every smooth point of `X`.** -/
private theorem exists_isIso_morphismRestrict_toBase (h : IsAdmissibleEmbedding sA i) {x : X}
    (hx : x ∈ smoothLocus (i ≫ sA)) : ∃ W : X.Opens, x ∈ W ∧
      W ≤ smoothLocus (i ≫ sA) ∧ IsIso ((embeddedResolution sA i).toBase ∣_ W) := by
  obtain ⟨U, η, hxU, hUcl, hU, hηU⟩ := exists_clopen_component h x
  obtain ⟨B, C, e, Ψ, he, hΨ, -, -, -, hiso⟩ := exists_component_data h U hUcl hU η hηU
  obtain ⟨x', rfl⟩ : x ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hxU
  obtain ⟨V, hxV, hV⟩ := hiso x' hx
  have h1 : IsIso ((((embeddedResolution sA i).toBase ∣_ U) ≫ e.hom) ∣_ V) := by
    rw [← hΨ, morphismRestrict_comp]
    have : IsIso (Ψ.hom ∣_ (((B.truncate (B.entryIndex (i η))).restrict C).toBase ⁻¹ᵁ V)) :=
      inferInstance
    exact IsIso.comp_isIso' this hV
  rw [morphismRestrict_comp] at h1
  have h2 : IsIso (((embeddedResolution sA i).toBase ∣_ U) ∣_ (e.hom ⁻¹ᵁ V)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ (e.hom ∣_ V) inferInstance h1
  have h3 : IsIso ((embeddedResolution sA i).toBase ∣_ (U.ι ''ᵁ (e.hom ⁻¹ᵁ V))) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict _ U _)).mp h2
  exact ⟨(U.ι ''ᵁ (e.hom ⁻¹ᵁ V)) ⊓ smoothLocus (i ≫ sA), ⟨⟨x', hxV, rfl⟩, hx⟩, inf_le_right,
    @Kollar.isIso_morphismRestrict_of_le _ _ _ _ _ inf_le_left h3⟩

/-- **`Π⁻¹(Sing X)` is snc at every point**: over a component `U`, `Ψ` carries it onto the
preimage of `Sing C` in `C_j`, which is the snc trace of the total exceptional set. -/
private theorem isSNCAt_preimage_singularLocus (h : IsAdmissibleEmbedding sA i)
    (y : (embeddedResolution sA i).target) :
    IsSNCAt ((embeddedResolution sA i).toBase ⁻¹' (singularLocus (i ≫ sA) : Set X)) y := by
  have : IsClosedImmersion i := h.2.2.2.1
  have : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  have : QuasiCompact sA := (embeddingTriple_mem_sncTriples h).2.2.2.1
  obtain ⟨U, η, hyU, hUcl, hU, hηU⟩ :=
    exists_clopen_component h ((embeddedResolution sA i).toBase y)
  obtain ⟨B, C, e, Ψ, he, hΨ, hCj, hsing, hsnc, -⟩ := exists_component_data h U hUcl hU η hηU
  have : IsLocallyNoetherian C.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.subschemeι ≫ sA)
  rw [← hsing] at hsnc
  generalize (B.truncate (B.entryIndex (i η))).restrict C = T at Ψ hΨ hCj hsnc
  have : IsProper T.toBase := isProper_toBase _
  have : CompactSpace T.target :=
    QuasiCompact.compactSpace_of_compactSpace (T.toBase ≫ C.subschemeι ≫ sA)
  have : IsLocallyNoetherian T.target :=
    LocallyOfFiniteType.isLocallyNoetherian (T.toBase ≫ C.subschemeι ≫ sA)
  have : AlgebraicGeometry.IsNoetherian T.target := {}
  have hz := isSNCAt_of_isSNCClosedSubset hsnc (Ψ.hom ⟨y, hyU⟩)
  have := hz.preimage Ψ.hom
  rw [preimage_preimage_singularLocus he hΨ] at this
  exact isSNCAt_of_isOpenImmersion _ this

end Data

/-- A morphism is an isomorphism over an open `V` if every point of `V` has an open neighbourhood
inside `V` over which it is an isomorphism. -/
private theorem isIso_morphismRestrict_of_forall_exists {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (V : Z.Opens) (H : ∀ x ∈ V, ∃ W : Z.Opens, x ∈ W ∧ W ≤ V ∧ IsIso (f ∣_ W)) :
    IsIso (f ∣_ V) := by
  choose W hxW hWle hWiso using fun x : V => H x.1 x.2
  have hcov : (⨆ x : V, V.ι ⁻¹ᵁ W x) = ⊤ :=
    eq_top_iff.2 fun z _ => Opens.mem_iSup.mpr ⟨z, hxW z⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ hcov).mpr fun z => ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict _ _ _)).mpr ?_
  have : V.ι ''ᵁ (V.ι ⁻¹ᵁ W z) = W z := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hWle z)
  change IsIso (f ∣_ (V.ι ''ᵁ (V.ι ⁻¹ᵁ W z)))
  rw [this]
  exact hWiso z

end Proof_lem_kr3f_embedded_resolution_strong

namespace MMP.Resolution

open Proof_lem_kr3f_embedded_resolution_strong

/-- **Strong resolution of an admissibly embedded affine disjoint union of varieties**
(Kollár p. 146, Thm. 3.36(1)–(3) for affine schemes). If `i : X ⟶ A` is an admissible embedding
(`IsAdmissibleEmbedding sA i`) and `Π = (embeddedResolution sA i).toBase`, then
1. the target of `Π` is smooth over `k`;
2. `Π` is an isomorphism over the smooth locus `smoothLocus (i ≫ sA)`;
3. `Π⁻¹(singularLocus (i ≫ sA))` is a divisor with simple normal crossings on the target. -/
@[mmp "lem_kr3f_embedded_resolution_strong"]
public theorem isSmoothScheme_and_isIso_and_isSNCClosedSubset_embeddedResolution
    {k : Type u} [Field k] {X A : Scheme.{u}} {sA : A ⟶ Spec (.of k)} {i : X ⟶ A}
    (h : IsAdmissibleEmbedding sA i) :
    IsSmoothScheme ((embeddedResolution sA i).toBase ≫ i ≫ sA) ∧
      IsIso ((embeddedResolution sA i).toBase ∣_ smoothLocus (i ≫ sA)) ∧
      IsSNCClosedSubset ((embeddedResolution sA i).toBase ≫ i ≫ sA)
        ((embeddedResolution sA i).toBase ⁻¹' (singularLocus (i ≫ sA) : Set X)) := by
  have : CharZero k := h.1
  have : IsClosedImmersion i := h.2.2.2.1
  have : LocallyOfFiniteType sA := (embeddingTriple_mem_sncTriples h).2.2.1
  have : QuasiCompact sA := (embeddingTriple_mem_sncTriples h).2.2.2.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sA)
  have : IsProper (embeddedResolution sA i).toBase := isProper_toBase _
  have : CompactSpace (embeddedResolution sA i).target :=
    QuasiCompact.compactSpace_of_compactSpace ((embeddedResolution sA i).toBase ≫ i ≫ sA)
  refine ⟨eq_top_iff.2 fun y _ => mem_smoothLocus_toBase h y,
    isIso_morphismRestrict_of_forall_exists _ _ fun _ => exists_isIso_morphismRestrict_toBase h,
    isSNCClosedSubset_of_forall_isSNCAt _ ((singularLocus (i ≫ sA)).isClosed.preimage
      (embeddedResolution sA i).toBase.continuous) (isSNCAt_preimage_singularLocus h)⟩

end MMP.Resolution
