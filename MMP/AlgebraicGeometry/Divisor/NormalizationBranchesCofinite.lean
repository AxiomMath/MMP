module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
public import MMP.AlgebraicGeometry.Normalization.Completion

/-!
# Finitely many subsets with several normalization branches

Let `Y` be a scheme of finite type over a field `k` and `Q = Q₁ ∪ ⋯ ∪ Q_m` a reduced union of
distinct prime divisors of `Y`. A *branch* of `Q` over an irreducible closed subset `V ⊆ Y` is a
prime divisor `P` of the normalization `Q_j^ν` of one of the `Q_j` (that is, of `∐_j Q_j^ν`)
whose image in `Y` is `V`. Away from the non-normal loci of the `Q_j` and their pairwise
intersections, which form a closed subset of codimension at least two in `Y`, the map
`∐_j Q_j^ν ⟶ Q` is an isomorphism; hence only finitely many `V` carry more than one branch.
Each such `V` is a component of the image of that locus.

## Main results

* `MMP.Fourfold.finite_setOf_nontrivial_normalizationBranches`: only finitely many irreducible
  closed `V ⊆ Y` carry more than one branch of `Q`.

## Implementation notes

* The union `Q` is a finite set of prime divisors `MMP.Mori.PrimeDivisor Y`; its members are
  distinct by construction. The normalization of a prime divisor `S`, with its map to `Y`, is
  `MMP.Fourfold.primeDivisorNormalization S`, and the prime divisors of `∐_j Q_j^ν` are the
  dependent pairs `(Q_j, P)` with `P` a prime divisor of `Q_j^ν`.
* "More than one branch" is `Set.Nontrivial` of the set of such pairs mapping onto `V`; this
  does not presuppose that the set is finite. That `V ⊆ Q` is implied, as a branch maps into
  `Q`.
* The source takes `Y` a normal variety; the statement is made for any `Y` of finite type over
  `k`, normality and separatedness of `Y` being unused.
* The source restricts to `V` of codimension two in `Y`; the statement is made for all
  irreducible closed `V`, the codimension-two case following by `Set.Finite.subset`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace MMP.Fourfold

/-- The normalization of an integral Nagata scheme is an isomorphism over a nonempty open. -/
private lemma exists_nonempty_isIso_normalization_restrict {X : Scheme.{u}} [IsIntegral X]
    (hN : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ IsIso (Scheme.normalization X hX ∣_ W) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨⟨U, hU⟩, hxU, hR⟩ := hN x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have hJ : IsJapaneseRing Γ(X, U) := MonogenicN1.isJapaneseRing_of_isNagataRing hR
  have hN1 : IsN1 Γ(X, U) := hJ.finite (FractionRing Γ(X, U))
  have : IsNoetherianRing Γ(X, U) := hR.1
  obtain ⟨⟨f, hf0, hf⟩, -⟩ :=
    (isN1_iff_exists_isIntegrallyClosed_away_and_forall_isN1_atPrime
      Γ(X, U)).mp hN1
  have hloc := hU.isLocalization_basicOpen f
  let e : Localization.Away f ≃ₐ[Γ(X, U)] Γ(X, X.basicOpen f) :=
    IsLocalization.algEquiv (Submonoid.powers f) _ _
  have hne : (X.basicOpen f : Set X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hf0 ((basicOpen_eq_bot_iff f).mp (Opens.ext (by simp [h])))
  have : Nonempty (X.basicOpen f) := hne.to_subtype
  have : IsDomain Γ(X, X.basicOpen f) := IsIntegral.component_integral _
  have : IsIntegrallyClosed Γ(X, X.basicOpen f) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  exact ⟨X.basicOpen f, hne, X.isIso_normalization_restrict_of_isNormalRing hX
    (hU.basicOpen f) (IsNormalRing.of_isIntegrallyClosed _)⟩

/-- If `x ⤳ y` are distinct points and `y` has coheight one, then `x` has coheight zero. -/
private lemma coheight_eq_zero_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hne : x ≠ y) (hy : Order.coheight y = 1) : Order.coheight x = 0 := by
  have hlt : y < x := lt_of_le_not_ge (show y ≤ x from h) (fun h' => hne (h.antisymm h').eq)
  have h1 := Order.coheight_add_one_le hlt
  rw [hy] at h1
  generalize Order.coheight x = a at h1 ⊢
  induction a using ENat.recTopCoe with
  | top => simp at h1
  | coe n =>
    norm_cast at h1 ⊢
    omega

/-- Every point of the support of a prime divisor specializes from its generic point. -/
private lemma genericPoint_specializes {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ P.support) : P.genericPoint ⤳ x :=
  specializes_iff_mem_closure.mpr (by rwa [← PrimeDivisor.support_eq_closure])

/-- Two prime divisors whose supports have the same image under a morphism have generic points
with the same image. -/
private lemma map_genericPoint_eq_of_image_support_eq {X Z : Scheme.{u}} (f : X ⟶ Z)
    {P P' : MMP.Mori.PrimeDivisor X} (h : f '' P.support = f '' P'.support) :
    f P.genericPoint = f P'.genericPoint := by
  have key : ∀ {P P' : MMP.Mori.PrimeDivisor X}, f '' P.support = f '' P'.support →
      f P.genericPoint ⤳ f P'.genericPoint := fun {P P'} h => by
    obtain ⟨x, hx, hxe⟩ : f P'.genericPoint ∈ f '' P.support :=
      h ▸ Set.mem_image_of_mem _ (MMP.Flips.primeDivisor_genericPoint_mem_support P')
    exact hxe ▸ (genericPoint_specializes P hx).map f.continuous
  exact ((key h).antisymm (key h.symm)).eq

/-- In an irreducible Noetherian scheme, only finitely many prime divisors lie in a given proper
closed subset. -/
private lemma finite_setOf_support_subset {X : Scheme.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {C : Set X} (hC : IsClosed C) (hCne : C ≠ Set.univ) :
    {P : MMP.Mori.PrimeDivisor X | P.support ⊆ C}.Finite := by
  obtain ⟨F, hFirr, hCF⟩ := NoetherianSpace.exists_finset_irreducible ⟨C, hC⟩
  let G : Set X := ⋃ k ∈ F, {x | IsGenericPoint x (k : Set X)}
  have hG : G.Finite := Set.Finite.biUnion F.finite_toSet fun _ _ =>
    Set.Subsingleton.finite fun _ ha _ hb => ha.eq hb
  refine Set.Finite.of_finite_image (hG.subset ?_) (PrimeDivisor.genericPoint_injective.injOn)
  rintro _ ⟨P, hP, rfl⟩
  have hgF : P.genericPoint ∈ ((F.sup id : Closeds X) : Set X) := by
    rw [← hCF]
    exact hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  obtain ⟨k, hkF, hgk⟩ : ∃ k ∈ F, P.genericPoint ∈ (k : Set X) := by
    simpa [Closeds.coe_finset_sup] using hgF
  have hkC : (k : Set X) ⊆ C := by
    have : k ≤ F.sup id := Finset.le_sup (f := id) hkF
    rw [← hCF] at this
    exact this
  obtain ⟨w, hw⟩ := QuasiSober.sober (hFirr ⟨k, hkF⟩) k.isClosed
  have hwg : w = P.genericPoint := by
    by_contra hne
    have hsp : w ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hw.symm ▸ hgk)
    have h0 := coheight_eq_zero_of_specializes hsp hne (PrimeDivisor.coheight_genericPoint P)
    rw [Order.coheight_eq_zero] at h0
    have hη := genericPoint_spec X
    have hle : w ≤ genericPoint X := hη.specializes (Set.mem_univ w)
    have heq : genericPoint X = w := (Specializes.antisymm hle (h0 hle)).eq
    apply hCne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hη.def, heq, hw.def]
    exact hkC
  exact Set.mem_biUnion hkF (show IsGenericPoint P.genericPoint (k : Set X) from hwg ▸ hw)

/-- The normalization `S^ν ⟶ S` of a prime divisor, without the closed immersion into `Y`. -/
private noncomputable abbrev nu {Y : Scheme.{u}} (S : MMP.Mori.PrimeDivisor Y) :
    primeDivisorNormalizationScheme S ⟶ S.idealSheaf.subscheme :=
  haveI := S.integral
  Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

/-- `primeDivisorNormalization S` is `nu S` followed by the closed immersion `S ⟶ Y`. -/
private lemma primeDivisorNormalization_eq {Y : Scheme.{u}} (S : MMP.Mori.PrimeDivisor Y) :
    primeDivisorNormalization S = nu S ≫ S.idealSheaf.subschemeι := rfl

/-- A prime divisor of a scheme locally of finite type over a field is Nagata. -/
private lemma isNagataScheme_subscheme {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsNagataScheme S.idealSheaf.subscheme :=
  isNagataScheme_of_locallyOfFiniteType_over_field k (S.idealSheaf.subschemeι ≫ sY)

/-- The normalization of a prime divisor of a scheme of finite type over a field is an
irreducible Noetherian space. -/
private lemma noetherianSpace_and_irreducibleSpace {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (S : MMP.Mori.PrimeDivisor Y) :
    NoetherianSpace (primeDivisorNormalizationScheme S) ∧
      IrreducibleSpace (primeDivisorNormalizationScheme S) := by
  haveI := S.integral
  have : IsIntegral (primeDivisorNormalizationScheme S) :=
    Scheme.isIntegral_normalizationScheme _
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have : IsFinite (nu S) := Scheme.isFinite_normalization (isNagataScheme_subscheme sY S)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  let p := nu S ≫ S.idealSheaf.subschemeι ≫ sY
  have : IsLocallyNoetherian (primeDivisorNormalizationScheme S) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (primeDivisorNormalizationScheme S) :=
    QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian (primeDivisorNormalizationScheme S) := AlgebraicGeometry.IsNoetherian.mk
  exact ⟨inferInstance, inferInstance⟩

/-- The normalization of a prime divisor is injective over a nonempty open, and some point of
that open lies on no other prime divisor. -/
private lemma exists_isOpen_injOn {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    ∃ W : Set S.idealSheaf.subscheme, IsOpen W ∧
      (∀ a b : primeDivisorNormalizationScheme S, nu S a ∈ W → nu S a = nu S b → a = b) ∧
      ∃ n : primeDivisorNormalizationScheme S, nu S n ∈ W ∧
        ∀ S' : MMP.Mori.PrimeDivisor Y, S' ≠ S → primeDivisorNormalization S n ∉ S'.support := by
  haveI := S.integral
  obtain ⟨W, hWne, hiso⟩ :=
    exists_nonempty_isIso_normalization_restrict (isNagataScheme_subscheme sY S)
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  let g := nu S ∣_ W
  have : IsIso g := hiso
  let h := TopCat.homeoOfIso (asIso g.base)
  refine ⟨W, W.isOpen, fun a b ha hab => ?_, ?_⟩
  · have hb : nu S b ∈ W := hab ▸ ha
    let a' : (nu S ⁻¹ᵁ W : Set _) := ⟨a, ha⟩
    let b' : (nu S ⁻¹ᵁ W : Set _) := ⟨b, hb⟩
    have : h a' = h b' := Subtype.ext ((morphismRestrict_base_coe (nu S) W a').trans
      (hab.trans (morphismRestrict_base_coe (nu S) W b').symm))
    exact congrArg Subtype.val (h.injective this)
  · have hη := genericPoint_spec S.idealSheaf.subscheme
    have hηW : genericPoint S.idealSheaf.subscheme ∈ W :=
      (hη.mem_open_set_iff W.isOpen).mpr (by simpa using hWne)
    obtain ⟨z, hz⟩ := h.surjective ⟨_, hηW⟩
    have hz' : nu S z.1 = genericPoint S.idealSheaf.subscheme :=
      (morphismRestrict_base_coe (nu S) W z).symm.trans (congrArg Subtype.val hz)
    refine ⟨z.1, hz' ▸ hηW, fun S' hS' hmem => hS' ?_⟩
    rw [primeDivisorNormalization_eq, Scheme.Hom.comp_apply, hz'] at hmem
    have hsub : S.support ⊆ S'.support := by
      intro y hy
      rw [PrimeDivisor.support, ← S.idealSheaf.range_subschemeι] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ((hη.specializes (Set.mem_univ x)).map
        S.idealSheaf.subschemeι.continuous).mem_closed S'.idealSheaf.support.isClosed hmem
    exact (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
      (hsub (MMP.Flips.primeDivisor_genericPoint_mem_support S))).symm

/-- Let `Y` be of finite type over a field `k` and `Q` a finite set of prime divisors of `Y`.
Only finitely many irreducible closed subsets `V ⊆ Y` are the image of more than one prime
divisor of `∐_{S ∈ Q} S^ν` under the normalizations `MMP.Fourfold.primeDivisorNormalization S`. -/
@[mmp "lem_oai4_c2_normalization_branch_cofinite"]
public theorem finite_setOf_nontrivial_normalizationBranches {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) :
    {V : IrreducibleCloseds Y |
      {B : Σ S : Q, MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1) |
        primeDivisorNormalization B.1.1 '' B.2.support = (V : Set Y)}.Nontrivial}.Finite := by
  choose W hWo hinj n hnW hnS using fun S : MMP.Mori.PrimeDivisor Y => exists_isOpen_injOn sY S
  let C : (S : Q) → Set (primeDivisorNormalizationScheme S.1) := fun S =>
    (nu S.1) ⁻¹' (W S.1)ᶜ ∪ ⋃ S' : Q, ⋃ (_ : S' ≠ S),
      primeDivisorNormalization S.1 ⁻¹' S'.1.support
  have hCcl : ∀ S, IsClosed (C S) := fun S =>
    ((hWo _).isClosed_compl.preimage (nu _).continuous).union
      (isClosed_iUnion_of_finite fun S' => isClosed_iUnion_of_finite fun _ =>
        S'.1.idealSheaf.support.isClosed.preimage (Scheme.Hom.continuous _))
  have hCne : ∀ S, C S ≠ Set.univ := fun S h => by
    have hmem : n S.1 ∈ C S := h ▸ Set.mem_univ _
    rcases hmem with h1 | h1
    · exact h1 (hnW S.1)
    · obtain ⟨S', hS', h2⟩ := Set.mem_iUnion₂.mp h1
      exact hnS S.1 S'.1 (fun e => hS' (Subtype.ext e)) h2
  have hfin : ∀ S : Q, {P : MMP.Mori.PrimeDivisor _ | P.support ⊆ C S}.Finite := fun S => by
    obtain ⟨_, _⟩ := noetherianSpace_and_irreducibleSpace sY S.1
    exact finite_setOf_support_subset (hCcl S) (hCne S)
  let Bad : Set (Σ S : Q, MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1)) :=
    ⋃ S : Q, Sigma.mk S '' {P | P.support ⊆ C S}
  have hBad : Bad.Finite := Set.finite_iUnion fun S => (hfin S).image _
  let F : (Σ S : Q, MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1)) →
      Set Y := fun B => primeDivisorNormalization B.1.1 '' B.2.support
  refine ((hBad.image F).preimage SetLike.coe_injective.injOn).subset ?_
  rintro V ⟨⟨S, P⟩, hB1, ⟨S2, P2⟩, hB2, hne⟩
  change primeDivisorNormalization S.1 '' P.support = (V : Set Y) at hB1
  change primeDivisorNormalization S2.1 '' P2.support = (V : Set Y) at hB2
  refine ⟨⟨S, P⟩, Set.mem_iUnion.mpr ⟨S, ⟨P, ?_, rfl⟩⟩, hB1⟩
  change P.support ⊆ C S
  by_cases hS : S2 = S
  · subst hS
    refine fun m hm => Or.inl fun hmW => hne (congrArg (Sigma.mk S2) ?_)
    have heq := map_genericPoint_eq_of_image_support_eq
      (primeDivisorNormalization S2.1) (hB1.trans hB2.symm)
    rw [primeDivisorNormalization_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at heq
    have heq' := S2.1.idealSheaf.subschemeι.isClosedEmbedding.injective heq
    have hgW : nu S2.1 P.genericPoint ∈ W S2.1 :=
      ((genericPoint_specializes P hm).map (nu S2.1).continuous).mem_open (hWo _) hmW
    exact PrimeDivisor.genericPoint_injective (hinj _ _ _ hgW heq')
  · refine fun m hm => Or.inr (Set.mem_iUnion₂.mpr ⟨S2, hS, ?_⟩)
    have : primeDivisorNormalization S.1 m ∈ (V : Set Y) :=
      hB1 ▸ Set.mem_image_of_mem _ hm
    rw [← hB2] at this
    exact (Set.image_subset_range _ _).trans
      (range_primeDivisorNormalization_subset S2.1) this

end MMP.Fourfold

end
