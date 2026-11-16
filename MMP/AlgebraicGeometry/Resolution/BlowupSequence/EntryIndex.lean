module

public import MMP.AlgebraicGeometry.Resolution.Principalization

/-!
# Entry indices and deletion of empty blow-ups in embedded resolution (Kollár, p. 137 and 3.32)

Let `𝐁 = (X_i, Z_i)_{i ≤ r}` be a blow-up sequence starting with a scheme `X`, `Π_i : X_i → X` the
composite of its first `i` blow-ups, and `j = j_𝐁(η)` the entry index of a point `η ∈ X`, the first
step whose centre meets the fibre of `Π_i` over `η`. Before the entry index nothing happens near
`η`: for every `i ≤ j` there is an open neighbourhood `V` of `η` over which `Π_i` is an
isomorphism. This follows by induction on `i` from the fact that a blow-up is an isomorphism off
its centre.

For a closed subscheme `X ⊆ A` and a blow-up sequence `𝐁` of `A`, the induced sequence
`𝓑𝓡_𝐁(X ⊆ A)` of `X` does not see the empty blow-ups of `𝐁`: after deleting the empty blow-ups
on both sides, `𝓑𝓡_{𝐁^red}(X ⊆ A)` and `𝓑𝓡_𝐁(X ⊆ A)` coincide (Kollár 3.32).

## Main statements

* `MMP.Resolution.Kollar.exists_isIso_truncate_toBase_restrict_of_le_entryIndex`: for
  `i ≤ j_𝐁(η)` there is an open `V ∋ η` such that `Π_i⁻¹(V) → V` is an isomorphism.
* `MMP.Resolution.Kollar.reduction_embeddedResolutionSequence_reduction`:
  `(𝓑𝓡_{𝐁^red}(X ⊆ A))^red = (𝓑𝓡_𝐁(X ⊆ A))^red`.

## Implementation notes

The first statement holds for any scheme `X`; the noetherian hypothesis of the source is not
needed. It is proved for the entry index `j_𝐁(S)` of an arbitrary subset `S ⊆ X`, with `V ⊇ S`:
if `Π'_i` is an isomorphism over an open `V' ⊇ π⁻¹(S)` of `B_{Z_0}X`, the open
`V = π(V' ∩ π⁻¹(X ∖ Z_0))` contains `S`, satisfies `π⁻¹(V) ⊆ V'`, and `π` is an isomorphism over
it.

For the second statement `X` is assumed noetherian (it is of finite type over a field in the
source). Along an isomorphism, deleting an empty blow-up shifts the entry indices by the number of
nonempty centres before them, so the active loci of `𝓑𝓡_{𝐁^red}` are those of `𝓑𝓡_𝐁` at the
nonempty steps, and the lengths `r_X` correspond. The two inductive constructions are then
compared step by step, the states being identified by isomorphisms: at an empty step of `𝐁` the
centre of `𝓑𝓡_𝐁` is empty; at a nonempty step both centres have the same inverse image, by
`MMP.Resolution.Kollar.comap_map_ι_of_isIso`, the open sets of pieces not yet frozen agreeing
there. Over a noetherian scheme the lift to the blown-up ambient scheme always exists, the
inverse image of the centre being the exceptional divisor.

## References

* [J. Kollár, *Lectures on resolution of singularities*, p. 137, 3.32]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution.Kollar

/-- A morphism that is an isomorphism over `W` is one over every open `V ≤ W`. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens}
    (hVW : V ≤ W) [IsIso (f ∣_ W)] : IsIso (f ∣_ V) := by
  have h : MorphismProperty.isomorphisms Scheme (f ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (MorphismProperty.isomorphisms.infer_property _) _
  replace h := (MorphismProperty.arrow_mk_iso_iff _
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ V))).mp h
  have hV : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVW
  exact (MorphismProperty.arrow_mk_iso_iff _ (morphismRestrictEq f hV)).mp h

open ClosedBlowupSequence in
/-- For `i ≤ j_𝐁(S)` the composite `Π_i` is an isomorphism over an open neighbourhood of `S`. -/
theorem exists_isIso_truncate_toBase_restrict_of_le_entryIndexOfSet {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (S : Set X) (i : ℕ) (hi : i ≤ B.entryIndexOfSet S) :
    ∃ V : X.Opens, S ⊆ V ∧ IsIso ((B.truncate i).toBase ∣_ V) := by
  induction B generalizing i with
  | nil Y =>
    refine ⟨⊤, fun _ _ => trivial, ?_⟩
    change IsIso (𝟙 Y ∣_ ⊤)
    infer_instance
  | @cons Y Z B ih =>
    cases i with
    | zero =>
      refine ⟨⊤, fun _ _ => trivial, ?_⟩
      change IsIso (𝟙 Y ∣_ ⊤)
      infer_instance
    | succ i =>
      have hS : ¬ ((Z.support : Set Y) ∩ S).Nonempty := by
        intro h
        simp only [entryIndexOfSet, h, ite_true] at hi
        omega
      have hi' : i ≤ B.entryIndexOfSet (blowUpToBase Z ⁻¹' S) := by
        simp only [entryIndexOfSet, hS, ite_false] at hi
        omega
      obtain ⟨V', hSV', hV'⟩ := ih _ i hi'
      set π := blowUpToBase Z
      let V₀ : Y.Opens := ⟨(Z.support : Set Y)ᶜ, Z.support.isClosed.isOpen_compl⟩
      have h₀ : IsIso (π ∣_ V₀) := isIso_blowUp_restrict_compl_support Z
      let g : V₀.toScheme ⟶ blowUp Z := inv (π ∣_ V₀) ≫ (π ⁻¹ᵁ V₀).ι
      have hg : g ≫ π = V₀.ι := by
        simp only [g, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
      have hgπ : (π ∣_ V₀) ≫ g = (π ⁻¹ᵁ V₀).ι := by simp [g]
      have key : ∀ p : V₀.toScheme, π (g p) = V₀.ι p := fun p => by
        rw [← Scheme.Hom.comp_apply, hg]
      have key' : ∀ q : (π ⁻¹ᵁ V₀).toScheme, g ((π ∣_ V₀) q) = (π ⁻¹ᵁ V₀).ι q := fun q => by
        rw [← Scheme.Hom.comp_apply, hgπ]
      let V : Y.Opens := V₀.ι ''ᵁ (g ⁻¹ᵁ V')
      have hπV : π ⁻¹ᵁ V ≤ V' := by
        rintro x ⟨y, hy, hyx⟩
        have hxV₀ : x ∈ π ⁻¹ᵁ V₀ := by
          change π x ∈ V₀
          rw [← hyx]
          exact y.2
        have e1 : (π ∣_ V₀) ⟨x, hxV₀⟩ = y :=
          Subtype.ext ((morphismRestrict_base_coe π V₀ ⟨x, hxV₀⟩).trans hyx.symm)
        have e2 := key' ⟨x, hxV₀⟩
        rw [e1] at e2
        change g y = x at e2
        rw [← e2]
        exact hy
      have hSV : S ⊆ V := by
        intro s hs
        have hs₀ : s ∈ V₀ := fun h => hS ⟨s, h, hs⟩
        refine ⟨⟨s, hs₀⟩, ?_, rfl⟩
        change g ⟨s, hs₀⟩ ∈ V'
        refine hSV' ?_
        change π (g ⟨s, hs₀⟩) ∈ S
        rwa [key ⟨s, hs₀⟩]
      refine ⟨V, hSV, ?_⟩
      change IsIso (((B.truncate i).toBase ≫ π) ∣_ V)
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' (isIso_morphismRestrict_of_le _ hπV)
        (isIso_morphismRestrict_of_le _ (V₀.ι_image_le _))

/-- **Blow-up sequences are isomorphisms before the entry index** (Kollár p. 137). -/
@[mmp "lem_kr3f_iso_before_entry"]
theorem exists_isIso_truncate_toBase_restrict_of_le_entryIndex {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (η : X) (i : ℕ) (hi : i ≤ B.entryIndex η) :
    ∃ V : X.Opens, η ∈ V ∧ IsIso ((B.truncate i).toBase ∣_ V) := by
  obtain ⟨V, hV, h⟩ := exists_isIso_truncate_toBase_restrict_of_le_entryIndexOfSet B {η} i hi
  exact ⟨V, hV rfl, h⟩

/-! ### Isomorphisms, inverse images and blow-ups -/

section Iso

open Scheme.IdealSheafData

/-- Pulling an ideal sheaf back along an isomorphism `f` and then along `f⁻¹` gives it back. -/
theorem comap_comap_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).comap (inv f) = I := by
  rw [← comap_comp, IsIso.inv_hom_id, comap_id]

/-- The inverse image of an ideal sheaf along an isomorphism `f` is its image along `f⁻¹`. -/
theorem comap_eq_map_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    I.comap f = I.map (inv f) := by
  apply le_antisymm
  · rw [le_map_iff_comap_le, comap_comap_inv]
  · have h : ((I.map (inv f)).comap (inv f)).comap f ≤ I.comap f :=
      comap_mono f (comap_map_le (I := I) (f := inv f))
    rwa [show ((I.map (inv f)).comap (inv f)).comap f = I.map (inv f) by
      rw [← comap_comp, IsIso.hom_inv_id, comap_id]] at h

/-- The inverse image of an ideal sheaf along an isomorphism is the unit ideal iff it is. -/
theorem comap_eq_top_iff_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (I : Y.IdealSheafData) : I.comap f = ⊤ ↔ I = ⊤ := by
  refine ⟨fun h => ?_, fun h => h ▸ comap_top f⟩
  rw [← comap_comap_inv f I, h, comap_top]

/-- Inverse image along an isomorphism commutes with scheme-theoretic image along an open
subscheme. -/
theorem comap_map_ι_of_isIso {Y' Y : Scheme.{u}} (φ : Y' ⟶ Y) [IsIso φ] (U : Y.Opens)
    (V : Y'.Opens) (hV : φ ⁻¹ᵁ U = V) (I : U.toScheme.IdealSheafData) :
    (I.map U.ι).comap φ = (I.comap (φ.resLE U V hV.ge)).map V.ι := by
  subst hV
  have hk : IsIso (φ.resLE U (φ ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  rw [comap_eq_map_inv φ, comap_eq_map_inv _, ← map_comp, ← map_comp]
  congr 1
  rw [IsIso.eq_inv_comp, Scheme.Hom.resLE_comp_ι_assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The blow-up of the empty closed subscheme is an isomorphism onto the base. -/
theorem isIso_blowUpToBase_of_eq_top {X : Scheme.{u}} {Z : X.IdealSheafData} (hZ : Z = ⊤) :
    IsIso (blowUpToBase Z) := by
  subst hZ
  exact isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    Stacks.Divisors.isEffectiveCartierDivisor_top

/-- The lift of an isomorphism `g` to the blow-up of the empty subscheme is an isomorphism. -/
theorem isIso_blowUpLift_of_eq_top {X Y : Scheme.{u}} {Z : X.IdealSheafData} (hZ : Z = ⊤)
    (g : Y ⟶ X) [IsIso g] (hc : Stacks.Blowup.IsCartierOver Z (Over.mk g)) :
    IsIso (blowUpLift Z g hc) := by
  have := isIso_blowUpToBase_of_eq_top hZ
  have h : IsIso (blowUpLift Z g hc ≫ blowUpToBase Z) := by
    rw [blowUpLift_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (blowUpToBase Z)

/-- Two morphisms to `B_ZX` over the same morphism `g`, along which `Z` is Cartier, are equal. -/
theorem blowUpLift_ext {X Y : Scheme.{u}} {Z : X.IdealSheafData} {g : Y ⟶ X}
    (hc : Stacks.Blowup.IsCartierOver Z (Over.mk g)) {f f' : Y ⟶ blowUp Z}
    (hf : f ≫ blowUpToBase Z = g) (hf' : f' ≫ blowUpToBase Z = g) : f = f' :=
  (blowUpLift_unique _ _ hc f hf).trans (blowUpLift_unique _ _ hc f' hf').symm

/-- The inverse image of `Z` on its blow-up `B_ZX` is an effective Cartier divisor. -/
theorem isCartierOver_blowUpToBase {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Stacks.Blowup.IsCartierOver Z (Over.mk (blowUpToBase Z)) :=
  Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z

/-- The canonical lift of an isomorphism is an isomorphism. -/
theorem isIso_canonicalLift {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ] (Z : X.IdealSheafData) :
    IsIso (canonicalLift ψ Z) := by
  have hc : Stacks.Blowup.IsCartierOver (Z.comap ψ) (Over.mk (blowUpToBase Z ≫ inv ψ)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor ((Z.comap ψ).comap (blowUpToBase Z ≫ inv ψ))
    rw [← comap_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact isCartierOver_blowUpToBase Z
  refine ⟨⟨blowUpLift _ _ hc, ?_, ?_⟩⟩
  · refine blowUpLift_ext (isCartierOver_blowUpToBase (Z.comap ψ)) ?_ (Category.id_comp _)
    rw [Category.assoc, blowUpLift_comp, ← Category.assoc, canonicalLift_comp_blowUpToBase,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · refine blowUpLift_ext (isCartierOver_blowUpToBase Z) ?_ (Category.id_comp _)
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- An isomorphism of schemes composed with its inverse is the identity on points. -/
theorem apply_inv_apply {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsIso ψ] (x : X) : ψ (inv ψ x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

end Iso

/-! ### Counting the nonempty centres -/

section Counting

open ClosedBlowupSequence

open Classical in
/-- The number of nonempty centres among the first `k` centres of a blow-up sequence. -/
def nonemptyCount : {X : Scheme.{u}} → ClosedBlowupSequence X → ℕ → ℕ
  | _, nil _, _ => 0
  | _, cons _ _, 0 => 0
  | _, cons Z B, k + 1 => nonemptyCount B k + if Z = ⊤ then 0 else 1

/-- The `k`-th centre of a blow-up sequence exists and is empty. -/
def IsEmptyAt : {X : Scheme.{u}} → ClosedBlowupSequence X → ℕ → Prop
  | _, nil _, _ => False
  | _, cons Z _, 0 => Z = ⊤
  | _, cons _ B, k + 1 => IsEmptyAt B k

/-- Truncating a blow-up sequence to its first `0` steps gives the empty sequence. -/
theorem truncate_zero {X : Scheme.{u}} (B : ClosedBlowupSequence X) : B.truncate 0 = nil X := by
  cases B <;> rfl

/-- There are no nonempty centres among the first `0` centres. -/
@[simp] theorem nonemptyCount_zero {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    nonemptyCount B 0 = 0 := by
  cases B <;> rfl

/-- The number of nonempty centres among the first `k` centres is monotone in `k`. -/
theorem nonemptyCount_mono {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    Monotone (nonemptyCount B) := by
  induction B with
  | nil X => exact fun _ _ _ => le_rfl
  | cons Z B ih =>
    intro a b hab
    cases a with
    | zero => simp [nonemptyCount_zero]
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [nonemptyCount]
        have := ih (Nat.le_of_succ_le_succ hab)
        omega

/-- If the `l`-th centre is empty, the count of nonempty centres does not grow at step `l`. -/
theorem nonemptyCount_succ_of_isEmptyAt {X : Scheme.{u}} (B : ClosedBlowupSequence X) (l : ℕ)
    (h : IsEmptyAt B l) : nonemptyCount B (l + 1) = nonemptyCount B l := by
  induction B generalizing l with
  | nil X => exact h.elim
  | cons Z B ih =>
    cases l with
    | zero =>
      change Z = ⊤ at h
      simp [nonemptyCount, nonemptyCount_zero, h]
    | succ l =>
      simp only [nonemptyCount]
      rw [ih l h]

/-- If the `l`-th centre exists and is nonempty, the count of nonempty centres grows by one. -/
theorem nonemptyCount_succ_of_not_isEmptyAt {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (l : ℕ) (hl : l < B.length) (h : ¬ IsEmptyAt B l) :
    nonemptyCount B (l + 1) = nonemptyCount B l + 1 := by
  induction B generalizing l with
  | nil X => simp [length] at hl
  | cons Z B ih =>
    cases l with
    | zero =>
      change ¬ Z = ⊤ at h
      simp [nonemptyCount, nonemptyCount_zero, h]
    | succ l =>
      simp only [length] at hl
      simp only [nonemptyCount]
      rw [ih l (by omega) h]
      omega

/-- The entry index of a subset is never the index of an empty centre. -/
theorem entryIndexOfSet_ne_of_isEmptyAt {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (S : Set X) (l : ℕ) (h : IsEmptyAt B l) : B.entryIndexOfSet S ≠ l := by
  induction B generalizing l with
  | nil X => exact h.elim
  | cons Z B ih =>
    have hS : ¬ ((Z.support : Set _) ∩ S).Nonempty → B.entryIndexOfSet (blowUpToBase Z ⁻¹' S) + 1
        = (cons Z B).entryIndexOfSet S := fun hn => by simp [entryIndexOfSet, hn]
    cases l with
    | zero =>
      change Z = ⊤ at h
      have hn : ¬ ((Z.support : Set _) ∩ S).Nonempty := by
        simp [h, Scheme.IdealSheafData.support_top]
      rw [← hS hn]
      omega
    | succ l =>
      by_cases hn : ((Z.support : Set _) ∩ S).Nonempty
      · simp [entryIndexOfSet, hn]
      · rw [← hS hn]
        have := ih (blowUpToBase Z ⁻¹' S) l h
        omega

/-- Along an isomorphism, deleting the empty blow-ups renumbers the entry index by the number of
nonempty centres before it. -/
theorem entryIndexOfSet_pullbackReduced_of_isIso {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (ψ : Y ⟶ X) [IsIso ψ] (S : Set X) :
    (B.pullbackReduced ψ).entryIndexOfSet (ψ ⁻¹' S) = nonemptyCount B (B.entryIndexOfSet S) := by
  induction B generalizing Y with
  | nil X => rfl
  | @cons X' Z B ih =>
    by_cases hZ : Z = ⊤
    · have hZ' : Z.comap ψ = ⊤ := (comap_eq_top_iff_of_isIso ψ Z).2 hZ
      simp only [pullbackReduced, hZ', dite_true]
      have := isIso_blowUpLift_of_eq_top hZ ψ (isCartierOver_of_comap_eq_top ψ Z hZ')
      have hS : ψ ⁻¹' S = blowUpLift Z ψ (isCartierOver_of_comap_eq_top ψ Z hZ') ⁻¹'
          (blowUpToBase Z ⁻¹' S) := by
        ext x
        simp only [Set.mem_preimage]
        rw [← Scheme.Hom.comp_apply, blowUpLift_comp]
      have hn : ¬ ((Z.support : Set _) ∩ S).Nonempty := by
        simp [hZ, Scheme.IdealSheafData.support_top]
      rw [hS, ih]
      simp only [entryIndexOfSet, hn, ite_false, nonemptyCount, eq_true hZ, ite_true,
        Nat.add_zero]
    · have hZ' : ¬ Z.comap ψ = ⊤ := fun h => hZ ((comap_eq_top_iff_of_isIso ψ Z).1 h)
      simp only [pullbackReduced, hZ', dite_false]
      have := isIso_canonicalLift ψ Z
      have hiff : (((Z.comap ψ).support : Set Y) ∩ ψ ⁻¹' S).Nonempty ↔
          ((Z.support : Set X') ∩ S).Nonempty := by
        rw [Scheme.IdealSheafData.support_comap]
        constructor
        · rintro ⟨y, hy, hyS⟩
          exact ⟨ψ y, hy, hyS⟩
        · rintro ⟨x, hx, hxS⟩
          refine ⟨inv ψ x, ?_, ?_⟩
          · change ψ (inv ψ x) ∈ (Z.support : Set X')
            rwa [apply_inv_apply]
          · change ψ (inv ψ x) ∈ S
            rwa [apply_inv_apply]
      by_cases hn : ((Z.support : Set X') ∩ S).Nonempty
      · simp only [entryIndexOfSet, hn, hiff.2 hn, ite_true, nonemptyCount_zero]
      · have hS : blowUpToBase (Z.comap ψ) ⁻¹' (ψ ⁻¹' S) = canonicalLift ψ Z ⁻¹'
            (blowUpToBase Z ⁻¹' S) := by
          ext x
          simp only [Set.mem_preimage]
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase]
        have hn' : ¬ (((Z.comap ψ).support : Set Y) ∩ ψ ⁻¹' S).Nonempty := fun h => hn (hiff.1 h)
        simp only [entryIndexOfSet, hn', hn, ite_false]
        rw [hS, ih]
        simp only [nonemptyCount, hZ, ite_false]

/-- Truncating and deleting the empty blow-ups commute, up to renumbering. -/
theorem truncate_pullbackReduced_of_isIso {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (ψ : Y ⟶ X) [IsIso ψ] (t : ℕ) :
    (B.truncate t).pullbackReduced ψ = (B.pullbackReduced ψ).truncate (nonemptyCount B t) := by
  induction B generalizing Y t with
  | nil X => rfl
  | cons Z B ih =>
    cases t with
    | zero => simp only [nonemptyCount_zero, truncate_zero]; rfl
    | succ t =>
      by_cases hZ : Z = ⊤
      · have hZ' : Z.comap ψ = ⊤ := (comap_eq_top_iff_of_isIso ψ Z).2 hZ
        have := isIso_blowUpLift_of_eq_top hZ ψ (isCartierOver_of_comap_eq_top ψ Z hZ')
        simp only [truncate, pullbackReduced, hZ', dite_true, nonemptyCount]
        rw [ih]
        simp only [eq_true hZ, ite_true, Nat.add_zero]
      · have hZ' : ¬ Z.comap ψ = ⊤ := fun h => hZ ((comap_eq_top_iff_of_isIso ψ Z).1 h)
        have := isIso_canonicalLift ψ Z
        simp only [truncate, pullbackReduced, hZ', dite_false, nonemptyCount]
        rw [ih]
        simp only [hZ, ite_false]
        rfl

/-- An index `k` of the truncation `𝐁_{≤ r}` is an index of `𝐁`, and the `k`-th centre of the
truncation is empty iff that of `𝐁` is. -/
theorem isEmptyAt_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) (r k : ℕ)
    (hk : k < (B.truncate r).length) :
    k < B.length ∧ (IsEmptyAt (B.truncate r) k ↔ IsEmptyAt B k) := by
  induction B generalizing r k with
  | nil X => simp [truncate, length] at hk
  | cons Z B ih =>
    cases r with
    | zero => simp [truncate, length] at hk
    | succ r =>
      cases k with
      | zero => exact ⟨by simp [length], Iff.rfl⟩
      | succ k =>
        simp only [truncate, length] at hk ⊢
        obtain ⟨h1, h2⟩ := ih r k (by omega)
        exact ⟨by omega, h2⟩

end Counting

/-! ### The embedded resolution sequence: truncation and active loci -/

section Embedded

open ClosedBlowupSequence

variable {X A : Scheme.{u}}

/-- Truncating the sequence produced by `ClosedBlowupSequence.embeddedAux` is running it along the
truncated sequence. -/
theorem embeddedAux_truncate (act : ℕ → X.Opens) {A' : Scheme.{u}}
    (C : ClosedBlowupSequence A') (n : ℕ) (Y : Scheme.{u}) (p : Y ⟶ X) (U : Y.Opens)
    (h : U.toScheme ⟶ A') (t : ℕ) :
    (embeddedAux act C n Y p U h).truncate t = embeddedAux act (C.truncate t) n Y p U h := by
  induction C generalizing n Y p U t with
  | nil A' => cases t <;> rfl
  | cons Z C ih =>
    cases t with
    | zero => rw [truncate_zero, truncate_zero]; rfl
    | succ t =>
      change _ = embeddedAux act (cons Z (C.truncate t)) n Y p U h
      simp only [embeddedAux]
      split_ifs with hc
      · rw [← ih]
        rfl
      · rfl

/-- The entry index of `a` for `𝐁^red` is the number of nonempty centres of `𝐁` before `j_𝐁(a)`. -/
theorem entryIndex_reduction (B : ClosedBlowupSequence A) (a : A) :
    B.reduction.entryIndex a = nonemptyCount B (B.entryIndex a) :=
  entryIndexOfSet_pullbackReduced_of_isIso B (𝟙 A) {a}

/-- The component entry index for `𝐁^red` is the number of nonempty centres of `𝐁` before the
component entry index for `𝐁`. -/
theorem componentEntryIndex_reduction (B : ClosedBlowupSequence A) (i : X ⟶ A) (x : X) :
    componentEntryIndex B.reduction i x = nonemptyCount B (componentEntryIndex B i x) := by
  unfold componentEntryIndex
  split_ifs <;> exact entryIndex_reduction B _

/-- The component entry index is never the index of an empty centre. -/
theorem componentEntryIndex_ne_of_isEmptyAt (B : ClosedBlowupSequence A) (i : X ⟶ A) (x : X)
    {l : ℕ} (hl : IsEmptyAt B l) : componentEntryIndex B i x ≠ l := by
  unfold componentEntryIndex
  split_ifs <;> exact entryIndexOfSet_ne_of_isEmptyAt B _ l hl

/-- The component entry index is at most the length of the sequence. -/
theorem componentEntryIndex_le_length (B : ClosedBlowupSequence A) (i : X ⟶ A) (x : X) :
    componentEntryIndex B i x ≤ B.length := by
  unfold componentEntryIndex
  split_ifs <;> exact B.entryIndex_le_length _

/-- Two active loci agree when the same points satisfy the corresponding strict inequalities on
component entry indices. -/
theorem activeLocus_congr {B B' : ClosedBlowupSequence A} {i : X ⟶ A} {n n' : ℕ}
    (h : ∀ x, n < componentEntryIndex B i x ↔ n' < componentEntryIndex B' i x) :
    activeLocus B i n = activeLocus B' i n' := by
  have hs : {x | n < componentEntryIndex B i x} = {x | n' < componentEntryIndex B' i x} :=
    Set.ext h
  unfold activeLocus
  exact hs ▸ rfl

/-- The active locus does not change at a step whose centre is empty. -/
theorem activeLocus_succ_of_isEmptyAt (B : ClosedBlowupSequence A) (i : X ⟶ A) {l : ℕ}
    (hl : IsEmptyAt B (l + 1)) : activeLocus B i (l + 1) = activeLocus B i l := by
  refine activeLocus_congr fun x => ?_
  have := componentEntryIndex_ne_of_isEmptyAt B i x hl
  omega

/-- If the first centre is empty, the active locus at step `0` is all of `X`. -/
theorem activeLocus_zero_of_isEmptyAt (B : ClosedBlowupSequence A) (i : X ⟶ A)
    (hl : IsEmptyAt B 0) : activeLocus B i 0 = ⊤ := by
  have hs : {x | 0 < componentEntryIndex B i x} = Set.univ := by
    ext x
    have := componentEntryIndex_ne_of_isEmptyAt B i x hl
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    omega
  have ho : IsOpen {x | 0 < componentEntryIndex B i x} := hs ▸ isOpen_univ
  unfold activeLocus
  simp only [ho, dite_true]
  ext x
  simp [hs]

/-- At a nonempty step `l`, the active locus of `𝐁` is that of `𝐁^red` at the renumbered step
`nonemptyCount B l`. -/
theorem activeLocus_reduction (B : ClosedBlowupSequence A) (i : X ⟶ A) {l : ℕ}
    (hl : l < B.length) (hne : ¬ IsEmptyAt B l) :
    activeLocus B.reduction i (nonemptyCount B l) = activeLocus B i l := by
  refine activeLocus_congr fun x => ?_
  rw [componentEntryIndex_reduction]
  have hs := nonemptyCount_succ_of_not_isEmptyAt B l hl hne
  have hm := nonemptyCount_mono B
  constructor
  · intro h
    by_contra h'
    have := hm (not_lt.1 h')
    omega
  · intro h
    have := hm (show l + 1 ≤ componentEntryIndex B i x from h)
    omega

/-- The length `r_X` for `𝐁^red` is the number of nonempty centres of `𝐁` among its first `r_X`
centres. -/
theorem embeddedResolutionLength_reduction (B : ClosedBlowupSequence A) (i : X ⟶ A) :
    embeddedResolutionLength B.reduction i = nonemptyCount B (embeddedResolutionLength B i) := by
  set S := {j | ∃ η : X, connectedComponent η ⊆ closure {η} ∧ j = B.entryIndex (i.base η)}
  have hR : {j | ∃ η : X, connectedComponent η ⊆ closure {η} ∧
      j = B.reduction.entryIndex (i.base η)} = nonemptyCount B '' S := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_image, S, entryIndex_reduction]
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨_, ⟨η, hη, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨η, hη, rfl⟩, rfl⟩
      exact ⟨η, hη, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨B.length, ?_⟩
    rintro _ ⟨η, -, rfl⟩
    exact B.entryIndex_le_length _
  change sSup _ = nonemptyCount B (sSup S)
  rw [hR]
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS, nonemptyCount_zero]
  · refine IsGreatest.csSup_eq ⟨⟨_, Nat.sSup_mem hS hbdd, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact nonemptyCount_mono B (le_csSup hbdd hj)

/-- `⨅_{l ≤ n} act l`. -/
def infUpTo (act : ℕ → X.Opens) : ℕ → X.Opens
  | 0 => act 0
  | n + 1 => infUpTo act n ⊓ act (n + 1)

/-- `⨅_{l ≤ 0} act l = act 0`. -/
@[simp] theorem infUpTo_zero (act : ℕ → X.Opens) : infUpTo act 0 = act 0 := rfl

/-- `⨅_{l ≤ n + 1} act l = (⨅_{l ≤ n} act l) ⊓ act (n + 1)`. -/
@[simp] theorem infUpTo_succ (act : ℕ → X.Opens) (n : ℕ) :
    infUpTo act (n + 1) = infUpTo act n ⊓ act (n + 1) := rfl

/-- `⨅_{l ≤ n} act l` is contained in `act n`. -/
theorem infUpTo_le (act : ℕ → X.Opens) (n : ℕ) : infUpTo act n ≤ act n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

/-- The bookkeeping of the active loci along the sequences `𝓑𝓡_𝐁` and `𝓑𝓡_{𝐁^red}`: the open
sets `E_B`, `E_R` of `X` over which the two runs are not yet frozen agree whenever a nonempty
centre is blown up. -/
def ActiveCompat (actB actR : ℕ → X.Opens) : {A' : Scheme.{u}} → ClosedBlowupSequence A' →
    ℕ → ℕ → X.Opens → X.Opens → Prop
  | _, nil _, _, _, _, _ => True
  | _, cons Z C, n, m, EB, ER =>
    (Z = ⊤ → ActiveCompat actB actR C (n + 1) m (EB ⊓ actB (n + 1)) ER) ∧
      (Z ≠ ⊤ → EB = ER ∧
        ActiveCompat actB actR C (n + 1) (m + 1) (EB ⊓ actB (n + 1)) (ER ⊓ actR (m + 1)))

/-- For `n < r`, the intersection of the active loci of `𝐁` up to step `n` is `X` if no centre up
to step `n` is nonempty, and otherwise equals the intersection of the active loci of `𝐁^red` up to
the last renumbered nonempty step. -/
theorem infUpTo_activeLocus_eq (B : ClosedBlowupSequence A) (i : X ⟶ A) (n : ℕ)
    (hn : n < B.length) :
    (nonemptyCount B (n + 1) = 0 ∧ infUpTo (activeLocus B i) n = ⊤) ∨
      (0 < nonemptyCount B (n + 1) ∧ infUpTo (activeLocus B i) n =
        infUpTo (activeLocus B.reduction i) (nonemptyCount B (n + 1) - 1)) := by
  induction n with
  | zero =>
    by_cases h0 : IsEmptyAt B 0
    · left
      rw [nonemptyCount_succ_of_isEmptyAt B 0 h0, nonemptyCount_zero]
      exact ⟨rfl, activeLocus_zero_of_isEmptyAt B i h0⟩
    · right
      rw [nonemptyCount_succ_of_not_isEmptyAt B 0 hn h0, nonemptyCount_zero]
      refine ⟨Nat.one_pos, ?_⟩
      change activeLocus B i 0 = activeLocus B.reduction i 0
      rw [← activeLocus_reduction B i hn h0, nonemptyCount_zero]
  | succ n ih =>
    have ih := ih (by omega)
    by_cases he : IsEmptyAt B (n + 1)
    · have hG : infUpTo (activeLocus B i) (n + 1) = infUpTo (activeLocus B i) n := by
        rw [infUpTo_succ, activeLocus_succ_of_isEmptyAt B i he]
        exact inf_eq_left.2 (infUpTo_le _ n)
      rw [nonemptyCount_succ_of_isEmptyAt B (n + 1) he, hG]
      exact ih
    · rw [nonemptyCount_succ_of_not_isEmptyAt B (n + 1) hn he]
      right
      refine ⟨Nat.succ_pos _, ?_⟩
      rw [infUpTo_succ, ← activeLocus_reduction B i hn he, Nat.add_sub_cancel]
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, top_inf_eq]
        rfl
      · obtain ⟨k, hk⟩ : ∃ k, nonemptyCount B (n + 1) = k + 1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
        rw [h2, hk, Nat.add_sub_cancel]
        rfl

/-- At a nonempty step `n`, the intersection of the active loci of `𝐁` up to `n` equals that of
`𝐁^red` up to the renumbered step `nonemptyCount B n`. -/
theorem infUpTo_activeLocus_eq_of_not_isEmptyAt (B : ClosedBlowupSequence A) (i : X ⟶ A)
    (n : ℕ) (hn : n < B.length) (hne : ¬ IsEmptyAt B n) :
    infUpTo (activeLocus B i) n = infUpTo (activeLocus B.reduction i) (nonemptyCount B n) := by
  have hs := nonemptyCount_succ_of_not_isEmptyAt B n hn hne
  rcases infUpTo_activeLocus_eq B i n hn with ⟨h1, -⟩ | ⟨-, h2⟩
  · omega
  · rw [h2, hs, Nat.add_sub_cancel]

/-- The active loci of `𝐁` and `𝐁^red` satisfy `ActiveCompat` along any sequence `𝐂` whose
empty centres are those of `𝐁` from step `n` on. -/
theorem activeCompat_of_tail (B : ClosedBlowupSequence A) (i : X ⟶ A) {A' : Scheme.{u}}
    (C : ClosedBlowupSequence A') (n : ℕ)
    (hC : ∀ k, k < C.length → n + k < B.length ∧ (IsEmptyAt C k ↔ IsEmptyAt B (n + k))) :
    ActiveCompat (activeLocus B i) (activeLocus B.reduction i) C n (nonemptyCount B n)
      (infUpTo (activeLocus B i) n) (infUpTo (activeLocus B.reduction i) (nonemptyCount B n)) := by
  induction C generalizing n with
  | nil A' => trivial
  | cons Z C ih =>
    obtain ⟨hlen, h0⟩ := hC 0 (by simp [length])
    have hC' : ∀ k, k < C.length → n + 1 + k < B.length ∧
        (IsEmptyAt C k ↔ IsEmptyAt B (n + 1 + k)) := fun k hk => by
      obtain ⟨h1, h2⟩ := hC (k + 1) (by simp only [length]; omega)
      rw [show n + 1 + k = n + (k + 1) by omega]
      exact ⟨h1, h2⟩
    refine ⟨fun hZ => ?_, fun hZ => ⟨?_, ?_⟩⟩
    · have := ih (n + 1) hC'
      rwa [nonemptyCount_succ_of_isEmptyAt B n (h0.1 hZ)] at this
    · exact infUpTo_activeLocus_eq_of_not_isEmptyAt B i n hlen (fun he => hZ (h0.2 he))
    · have := ih (n + 1) hC'
      rwa [nonemptyCount_succ_of_not_isEmptyAt B n hlen (fun he => hZ (h0.2 he))] at this

end Embedded

/-! ### Comparing `𝓑𝓡_𝐁` with `𝓑𝓡_{𝐁^red}` -/

section Compare

open ClosedBlowupSequence

/-- The blow-up of a noetherian scheme is noetherian. -/
theorem isNoetherian_blowUp' {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (W : Y.IdealSheafData) : AlgebraicGeometry.IsNoetherian (blowUp W) := by
  have h2 : IsLocallyNoetherian (blowUp W) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase W)
  have h3 : CompactSpace (blowUp W) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase W)
  exact @AlgebraicGeometry.IsNoetherian.mk _ h2 h3

/-- If the inverse image of `Z` along `g` is an effective Cartier divisor, so is its inverse image
along `q ≫ g` for an open immersion `q`. -/
theorem isCartierOver_comp_of_isOpenImmersion {T T' A : Scheme.{u}} (q : T' ⟶ T)
    [IsOpenImmersion q] (g : T ⟶ A) (Z : A.IdealSheafData)
    (hc : Stacks.Blowup.IsCartierOver Z (Over.mk g)) :
    Stacks.Blowup.IsCartierOver Z (Over.mk (q ≫ g)) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (q ≫ g))
  rw [Scheme.IdealSheafData.comap_comp]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _ hc q

/-- Over a noetherian scheme the inverse image of `Z_n` on `π_n⁻¹(U)` is the exceptional
divisor, so the lift in `ClosedBlowupSequence.embeddedAux` always exists. -/
theorem isCartierOver_resLE' {Y A' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (U : Y.Opens) (h : U.toScheme ⟶ A') (Z : A'.IdealSheafData)
    (U' : (blowUp ((Z.comap h).map U.ι)).Opens)
    (hle : U' ≤ blowUpToBase ((Z.comap h).map U.ι) ⁻¹ᵁ U) :
    Stacks.Blowup.IsCartierOver Z
      (Over.mk ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle ≫ h)) := by
  have hq : QuasiCompact U.ι := by
    have : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set Y)
    exact inferInstance
  have h1 : (Z.comap h) = ((Z.comap h).map U.ι).comap U.ι :=
    (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion U.ι (Z.comap h)).symm
  change Stacks.Divisors.IsEffectiveCartierDivisor
    (Z.comap (((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle) ≫ h))
  rw [Scheme.IdealSheafData.comap_comp,
    congrArg (fun J => J.comap ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle)) h1,
    ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι,
    Scheme.IdealSheafData.comap_comp]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) _

/-- Over a noetherian scheme, one step of `ClosedBlowupSequence.embeddedAux` along `cons Z C`
blows up `W = (h⁻¹Z).map U.ι` and continues along `C` with the lifted morphism. -/
theorem embeddedAux_cons {X : Scheme.{u}} (act : ℕ → X.Opens) {A' : Scheme.{u}}
    (Z : A'.IdealSheafData) (C : ClosedBlowupSequence (blowUp Z)) (n : ℕ) (Y : Scheme.{u})
    [AlgebraicGeometry.IsNoetherian Y] (p : Y ⟶ X) (U : Y.Opens) (h : U.toScheme ⟶ A') :
    embeddedAux act (cons Z C) n Y p U h = cons ((Z.comap h).map U.ι)
      (embeddedAux act C (n + 1) _ (blowUpToBase ((Z.comap h).map U.ι) ≫ p)
        (blowUpToBase ((Z.comap h).map U.ι) ⁻¹ᵁ U ⊓
          (blowUpToBase ((Z.comap h).map U.ι) ≫ p) ⁻¹ᵁ act (n + 1))
        (blowUpLift Z ((blowUpToBase ((Z.comap h).map U.ι)).resLE U _ inf_le_left ≫ h)
          (isCartierOver_resLE' U h Z _ inf_le_left))) := by
  rw [embeddedAux.eq_2,
    dite_eq_left_of_eq_true (eq_true (isCartierOver_resLE' U h Z _ inf_le_left))]

/-- If the inverse image of the first centre is empty, `pullbackReduced` skips that step. -/
theorem pullbackReduced_cons_of_eq_top {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) (hZ : Z.comap h = ⊤) :
    (cons Z B).pullbackReduced h =
      B.pullbackReduced (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) := by
  simp only [pullbackReduced, hZ, dite_true]

/-- If the inverse image of the first centre is nonempty, `pullbackReduced` keeps that step. -/
theorem pullbackReduced_cons_of_ne_top {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) (hZ : ¬ Z.comap h = ⊤) :
    (cons Z B).pullbackReduced h = cons (Z.comap h) (B.pullbackReduced (canonicalLift h Z)) := by
  simp only [pullbackReduced, hZ, dite_false]

/-- Transporting `pullbackReduced` after a first blow-up along an equality of centres. -/
theorem cons_pullbackReduced_congr {Y Y₁ : Scheme.{u}} {I I' : Y.IdealSheafData} (e : I = I')
    (T : ClosedBlowupSequence Y₁) (f : blowUp I' ⟶ Y₁) :
    cons I (T.pullbackReduced (eqToHom (congrArg blowUp e) ≫ f)) =
      cons I' (T.pullbackReduced f) := by
  subst e
  simp

/-- Transporting `blowUpToBase` along an equality of centres. -/
theorem eqToHom_blowUpToBase {Y : Scheme.{u}} {I I' : Y.IdealSheafData} (e : I = I') :
    eqToHom (congrArg blowUp e) ≫ blowUpToBase I' = blowUpToBase I := by
  subst e
  simp

/-- `resLE` of a composite `ψ ≫ φ` is the composite of the `resLE` of `ψ` and of `φ`. -/
theorem resLE_eq_comp {T T' S : Scheme.{u}} {f : T ⟶ S} {ψ : T ⟶ T'} {φ : T' ⟶ S}
    (hf : f = ψ ≫ φ) (U : S.Opens) (V : T'.Opens) (W : T.Opens) (e : W ≤ f ⁻¹ᵁ U)
    (eV : V ≤ φ ⁻¹ᵁ U) (eW : W ≤ ψ ⁻¹ᵁ V) :
    f.resLE U W e = ψ.resLE V W eW ≫ φ.resLE U V eV := by
  subst hf
  rw [Scheme.Hom.resLE_comp_resLE]

/-- The inverse image of `E ⊓ G` along `φ ≫ p` lies in that of `E`. -/
theorem preimage_comp_inf_le_preimage_preimage {T Y X : Scheme.{u}} (φ : T ⟶ Y) (p : Y ⟶ X)
    (E G : X.Opens) :
    (φ ≫ p) ⁻¹ᵁ (E ⊓ G) ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ E) :=
  fun _ hx => hx.1

/-- The inverse image of `E ⊓ F ⊓ G` along `φ ≫ b ≫ p` lies in that of `E ⊓ F`. -/
theorem preimage_comp_comp_inf_inf_le {T Y₁ Y₀ X : Scheme.{u}} (φ : T ⟶ Y₁) (b : Y₁ ⟶ Y₀)
    (p : Y₀ ⟶ X) (E F G : X.Opens) :
    (φ ≫ b ≫ p) ⁻¹ᵁ (E ⊓ F ⊓ G) ≤ φ ⁻¹ᵁ (b ⁻¹ᵁ (p ⁻¹ᵁ E) ⊓ (b ≫ p) ⁻¹ᵁ F) :=
  fun _ hx => hx.1

/-- For `f = g ≫ p`, the inverse image of `E ⊓ G` along `f` lies in that of `G`. -/
theorem preimage_inf_le_preimage_preimage_of_eq_comp {T Y X : Scheme.{u}} {f : T ⟶ X} {g : T ⟶ Y}
    {p : Y ⟶ X} (h : f = g ≫ p) (E G : X.Opens) : f ⁻¹ᵁ (E ⊓ G) ≤ g ⁻¹ᵁ (p ⁻¹ᵁ G) := by
  subst h
  exact fun _ hx => hx.2

/-- For `f = φ ≫ b ≫ p`, the inverse image of `E' ⊓ (E ⊓ F)` along `f` lies in that of `E ⊓ F`. -/
theorem preimage_inf_inf_le_of_eq_comp_comp {T Y₁ Y₀ X : Scheme.{u}} {f : T ⟶ X} (φ : T ⟶ Y₁)
    (b : Y₁ ⟶ Y₀) (p : Y₀ ⟶ X) (h : f = φ ≫ b ≫ p) (E E' F : X.Opens) :
    f ⁻¹ᵁ (E' ⊓ (E ⊓ F)) ≤ φ ⁻¹ᵁ (b ⁻¹ᵁ (p ⁻¹ᵁ E) ⊓ (b ≫ p) ⁻¹ᵁ F) := by
  subst h
  exact fun _ hx => hx.2

/-- For `f = ψ ≫ φ ≫ p`, `E' ≤ E` and `G' ≤ G`, the inverse image of `E' ⊓ G'` along `f` lies in
that of `E ⊓ G` along `φ ≫ p`. -/
theorem preimage_inf_le_preimage_comp_inf_of_le {T T' Y X : Scheme.{u}} {f : T ⟶ X} (ψ : T ⟶ T')
    (φ : T' ⟶ Y) (p : Y ⟶ X) (h : f = ψ ≫ φ ≫ p) {E E' G G' : X.Opens} (hE : E' ≤ E) (hG : G' ≤ G) :
    f ⁻¹ᵁ (E' ⊓ G') ≤ ψ ⁻¹ᵁ ((φ ≫ p) ⁻¹ᵁ (E ⊓ G)) := by
  subst h
  exact fun _ hx => ⟨hE hx.1, hG hx.2⟩

/-- The restriction `resLE` of an isomorphism is an open immersion. -/
instance isOpenImmersion_resLE_of_isIso {T S : Scheme.{u}} (f : T ⟶ S) [IsIso f] (U : S.Opens)
    (V : T.Opens) (e : V ≤ f ⁻¹ᵁ U) : IsOpenImmersion (f.resLE U V e) := by
  rw [Scheme.Hom.resLE]
  infer_instance

/-- Deleting the empty blow-ups along two isomorphisms `φ₁`, `φ₂` from `Y'` after a first blow-up
with the same inverse image on `Y'` gives the same result as soon as it does for the remaining
sequences, along any pair of isomorphisms over a common `ψ : Y'' → Y'`. -/
theorem pullbackReduced_cons_congr {Y₁ Y₂ Y' : Scheme.{u}} {W₁ : Y₁.IdealSheafData}
    {W₂ : Y₂.IdealSheafData} (T₁ : ClosedBlowupSequence (blowUp W₁))
    (T₂ : ClosedBlowupSequence (blowUp W₂)) (φ₁ : Y' ⟶ Y₁) [IsIso φ₁] (φ₂ : Y' ⟶ Y₂) [IsIso φ₂]
    (hI : W₁.comap φ₁ = W₂.comap φ₂)
    (H : ∀ {Y'' : Scheme.{u}} (ψ : Y'' ⟶ Y') (f₁ : Y'' ⟶ blowUp W₁) (f₂ : Y'' ⟶ blowUp W₂),
      IsIso f₁ → IsIso f₂ → f₁ ≫ blowUpToBase W₁ = ψ ≫ φ₁ → f₂ ≫ blowUpToBase W₂ = ψ ≫ φ₂ →
        T₁.pullbackReduced f₁ = T₂.pullbackReduced f₂) :
    (cons W₁ T₁).pullbackReduced φ₁ = (cons W₂ T₂).pullbackReduced φ₂ := by
  by_cases h : W₁.comap φ₁ = ⊤
  · have h' : W₂.comap φ₂ = ⊤ := hI ▸ h
    rw [pullbackReduced_cons_of_eq_top _ _ _ h, pullbackReduced_cons_of_eq_top _ _ _ h']
    exact H (𝟙 Y') _ _
      (isIso_blowUpLift_of_eq_top ((comap_eq_top_iff_of_isIso φ₁ W₁).1 h) φ₁ _)
      (isIso_blowUpLift_of_eq_top ((comap_eq_top_iff_of_isIso φ₂ W₂).1 h') φ₂ _)
      (by rw [blowUpLift_comp, Category.id_comp]) (by rw [blowUpLift_comp, Category.id_comp])
  · have h' : ¬ W₂.comap φ₂ = ⊤ := hI ▸ h
    rw [pullbackReduced_cons_of_ne_top _ _ _ h, pullbackReduced_cons_of_ne_top _ _ _ h',
      ← cons_pullbackReduced_congr hI]
    have := isIso_canonicalLift φ₂ W₂
    exact congrArg (cons _) (H (blowUpToBase (W₁.comap φ₁)) _ _ (isIso_canonicalLift φ₁ W₁)
      inferInstance (canonicalLift_comp_blowUpToBase _ _)
      (by rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        eqToHom_blowUpToBase hI]))

/-- The comparison of the two runs of `ClosedBlowupSequence.embeddedAux`: one along a blow-up
sequence `𝐂`, one along `𝐂` with its empty blow-ups deleted (pulled back along an isomorphism
`α`), from states identified by isomorphisms `φ_B`, `φ_R`; after deleting the empty blow-ups
they agree. -/
theorem pullbackReduced_embeddedAux_eq {X : Scheme.{u}} (actB actR : ℕ → X.Opens)
    {AB : Scheme.{u}} (CB : ClosedBlowupSequence AB) :
    ∀ {AR : Scheme.{u}} (α : AR ⟶ AB) [IsIso α] (nB nR : ℕ) (EB ER : X.Opens)
      {YB YR Y' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian YB]
      [AlgebraicGeometry.IsNoetherian YR] (pB : YB ⟶ X) (pR : YR ⟶ X)
      (UB : YB.Opens) (UR : YR.Opens) (hB : UB.toScheme ⟶ AB) (hR : UR.toScheme ⟶ AR)
      (φB : Y' ⟶ YB) [IsIso φB] (φR : Y' ⟶ YR) [IsIso φR],
      ActiveCompat actB actR CB nB nR EB ER → φB ≫ pB = φR ≫ pR →
      UB = pB ⁻¹ᵁ EB → UR = pR ⁻¹ᵁ ER →
      ∀ (hle : (φB ≫ pB) ⁻¹ᵁ (EB ⊓ ER) ≤ φB ⁻¹ᵁ UB)
        (hle' : (φB ≫ pB) ⁻¹ᵁ (EB ⊓ ER) ≤ φR ⁻¹ᵁ UR),
      φB.resLE UB _ hle ≫ hB = φR.resLE UR _ hle' ≫ hR ≫ α →
      (embeddedAux actB CB nB YB pB UB hB).pullbackReduced φB =
        (embeddedAux actR (CB.pullbackReduced α) nR YR pR UR hR).pullbackReduced φR := by
  induction CB with
  | nil AB =>
    intros
    rfl
  | @cons AB' Z C ih =>
    intro AR α _ nB nR EB ER YB YR Y' _ _ pB pR UB UR hB hR φB _ φR _ hA hp hUB hUR hle hle' hh
    subst hUB hUR
    by_cases hZ : Z = ⊤
    · have hZα : Z.comap α = ⊤ := by rw [hZ, Scheme.IdealSheafData.comap_top]
      rw [pullbackReduced_cons_of_eq_top _ C α hZα, embeddedAux_cons]
      have hWt : (Z.comap hB).map (pB ⁻¹ᵁ EB).ι = ⊤ := by
        rw [hZ, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.map_top]
      have hWφ := (comap_eq_top_iff_of_isIso φB _).2 hWt
      rw [pullbackReduced_cons_of_eq_top _ _ φB hWφ]
      have := isNoetherian_blowUp' ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι)
      have := isIso_blowUpLift_of_eq_top hZ α (isCartierOver_of_comap_eq_top α Z hZα)
      set φB'' := blowUpLift _ φB (isCartierOver_of_comap_eq_top φB _ hWφ) with hφB''
      have hiB : IsIso φB'' := isIso_blowUpLift_of_eq_top hWt φB _
      have hφ : φB'' ≫ blowUpToBase ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι) = φB := blowUpLift_comp _ _ _
      have hp' : φB'' ≫ blowUpToBase ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι) ≫ pB = φB ≫ pB := by
        rw [← Category.assoc, hφ]
      have hp'' := hp'.trans hp
      refine ih _ (nB + 1) nR (EB ⊓ actB (nB + 1)) ER _ pR _ _ _ hR φB'' φR (hA.1 hZ) hp'' rfl
        rfl (preimage_comp_comp_inf_inf_le _ _ _ _ _ _)
        (preimage_inf_le_preimage_preimage_of_eq_comp hp'' _ _) ?_
      refine blowUpLift_ext ?_ (by rw [Category.assoc, blowUpLift_comp]) ?_
      · exact @isCartierOver_comp_of_isOpenImmersion _ _ _ _
          (@isOpenImmersion_resLE_of_isIso _ _ _ hiB _ _ _) _ _
          (isCartierOver_resLE' _ hB Z _ inf_le_left)
      · have e4 := preimage_inf_le_preimage_comp_inf_of_le
          (f := φB'' ≫ blowUpToBase ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι) ≫ pB) (𝟙 Y') φB pB
          (by rw [hp', Category.id_comp])
          (E := EB) (G := ER) (E' := EB ⊓ actB (nB + 1)) inf_le_left le_rfl
        rw [Category.assoc, Category.assoc, blowUpLift_comp, Scheme.Hom.resLE_comp_resLE_assoc,
          resLE_eq_comp (hφ.trans (Category.id_comp _).symm) _ _ _ _ hle e4,
          resLE_eq_comp (Category.id_comp φR).symm _ _ _ _ hle' e4]
        simp only [Category.assoc, hh]
    · obtain ⟨rfl, hA'⟩ := hA.2 hZ
      have hZα : ¬ Z.comap α = ⊤ := fun h => hZ ((comap_eq_top_iff_of_isIso α Z).1 h)
      have := isIso_canonicalLift α Z
      rw [pullbackReduced_cons_of_ne_top _ C α hZα, embeddedAux_cons, embeddedAux_cons]
      have := isNoetherian_blowUp' ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι)
      have := isNoetherian_blowUp' (((Z.comap α).comap hR).map (pR ⁻¹ᵁ EB).ι)
      have hVB : φB ⁻¹ᵁ (pB ⁻¹ᵁ EB) = (φB ≫ pB) ⁻¹ᵁ (EB ⊓ EB) := by rw [inf_idem]; rfl
      have hVR : φR ⁻¹ᵁ (pR ⁻¹ᵁ EB) = (φB ≫ pB) ⁻¹ᵁ (EB ⊓ EB) := by rw [inf_idem, hp]; rfl
      refine pullbackReduced_cons_congr _ _ φB φR ?_ ?_
      · rw [comap_map_ι_of_isIso φB _ _ hVB, comap_map_ι_of_isIso φR _ _ hVR,
          ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          ← Scheme.IdealSheafData.comap_comp, hh, Category.assoc]
      intro Y'' ψ φB'' φR'' hiB hiR hφB hφR
      have hp'' : φB'' ≫ blowUpToBase ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι) ≫ pB =
          φR'' ≫ blowUpToBase (((Z.comap α).comap hR).map (pR ⁻¹ᵁ EB).ι) ≫ pR := by
        rw [← Category.assoc, hφB, ← Category.assoc, hφR, Category.assoc, Category.assoc, hp]
      refine ih _ (nB + 1) (nR + 1) (EB ⊓ actB (nB + 1)) (EB ⊓ actR (nR + 1)) _ _ _ _ _ _ φB''
        φR'' hA' hp'' rfl rfl (preimage_comp_comp_inf_inf_le _ _ _ _ _ _)
        (preimage_inf_inf_le_of_eq_comp_comp _ _ _ hp'' _ _ _) ?_
      refine blowUpLift_ext ?_ (by rw [Category.assoc, blowUpLift_comp]) ?_
      · exact @isCartierOver_comp_of_isOpenImmersion _ _ _ _
          (@isOpenImmersion_resLE_of_isIso _ _ _ hiB _ _ _) _ _
          (isCartierOver_resLE' _ hB Z _ inf_le_left)
      · have e4 := preimage_inf_le_preimage_comp_inf_of_le
          (f := φB'' ≫ blowUpToBase ((Z.comap hB).map (pB ⁻¹ᵁ EB).ι) ≫ pB) ψ φB pB
          (by rw [← Category.assoc, hφB, Category.assoc]) (E := EB) (G := EB)
          (E' := EB ⊓ actB (nB + 1)) (G' := EB ⊓ actR (nR + 1)) inf_le_left inf_le_left
        rw [Category.assoc, Category.assoc, canonicalLift_comp_blowUpToBase,
          ← Category.assoc (blowUpLift _ _ _), blowUpLift_comp]
        simp only [Category.assoc]
        rw [Scheme.Hom.resLE_comp_resLE_assoc, Scheme.Hom.resLE_comp_resLE_assoc,
          resLE_eq_comp hφR _ _ _ _ hle' e4, resLE_eq_comp hφB _ _ _ _ hle e4]
        simp only [Category.assoc, hh]

/-- The two restrictions of `𝟙 X` to `V ≤ U` and `V ≤ U'`, composed with the inclusions and with
`i`, agree. -/
theorem resLE_id_comp_ι {X A : Scheme.{u}} (U U' V : X.Opens) (e : V ≤ 𝟙 X ⁻¹ᵁ U)
    (e' : V ≤ 𝟙 X ⁻¹ᵁ U') (i : X ⟶ A) :
    Scheme.Hom.resLE (𝟙 X) U V e ≫ U.ι ≫ i =
      Scheme.Hom.resLE (𝟙 X) U' V e' ≫ (U'.ι ≫ i) ≫ 𝟙 A := by
  simp only [Category.comp_id, Scheme.Hom.resLE_comp_ι_assoc]

/-- **Deleting the empty blow-ups of the ambient sequence** (Kollár 3.32): for a blow-up sequence
`𝐁` of `A` and `i : X → A` with `X` noetherian, `(𝓑𝓡_{𝐁^red}(X ⊆ A))^red = (𝓑𝓡_𝐁(X ⊆ A))^red`. -/
@[mmp "lem_kr3f_br_delete_empty"]
theorem reduction_embeddedResolutionSequence_reduction {X A : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (B : ClosedBlowupSequence A) (i : X ⟶ A) :
    (embeddedResolutionSequence B.reduction i).reduction =
      (embeddedResolutionSequence B i).reduction := by
  unfold embeddedResolutionSequence
  rw [embeddedAux_truncate, embeddedAux_truncate, embeddedResolutionLength_reduction]
  have hseq : B.reduction.truncate (nonemptyCount B (embeddedResolutionLength B i)) =
      (B.truncate (embeddedResolutionLength B i)).pullbackReduced (𝟙 A) :=
    (truncate_pullbackReduced_of_isIso B (𝟙 A) _).symm
  rw [hseq]
  have hA := activeCompat_of_tail B i (B.truncate (embeddedResolutionLength B i)) 0
    (fun k hk => by simpa using isEmptyAt_truncate B _ k hk)
  rw [nonemptyCount_zero] at hA
  refine (pullbackReduced_embeddedAux_eq (activeLocus B i) (activeLocus B.reduction i) _ (𝟙 A)
    0 0 _ _ (𝟙 X) (𝟙 X) _ _ _ _ (𝟙 X) (𝟙 X) hA rfl rfl rfl
    (preimage_comp_inf_le_preimage_preimage _ _ _ _)
    (preimage_inf_le_preimage_preimage_of_eq_comp rfl _ _) ?_).symm
  exact resLE_id_comp_ι _ _ _ _ _ i

end Compare

end MMP.Resolution.Kollar
