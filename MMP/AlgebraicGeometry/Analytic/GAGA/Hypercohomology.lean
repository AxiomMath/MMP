module

public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveCohomology
import MMP.Topology.Sheaves.GodementFlasqueResolution

/-!
# GAGA for hypercohomology of complexes with `ℂ`-linear differentials

Let `X` be a projective scheme over `ℂ` and `K^•` a bounded complex whose terms are coherent
`𝒪_X`-modules `F p` and whose differentials `δ^p : F p → F (p + 1)` are maps of sheaves of
complex vector spaces (not necessarily `𝒪_X`-linear, e.g. the exterior derivative of a de Rham
complex). Suppose the analytifications `(F p)^an` carry differentials `δ^{p,an}` of abelian
sheaves making `ι : α_X⁻¹ K^• → K^{•,an}`, termwise `ι_{F p}`, a morphism of complexes. Then
`ℍ^n(X, K^•) → ℍ^n(X^an, α_X⁻¹ K^•) → ℍ^n(X^an, K^{•,an})`, the pullback along `α_X`
followed by `ι_*`, is an isomorphism for every `n`, and on the graded pieces `F p [-p]` of
the stupid filtrations it is the comparison map `c^{n-p}_{F p}`.

## Main results

* `MMP.Analytic.isIso_hypercohomologyComparison_of_isProjective_of_bounded`: the
  comparison of hypercohomology is an isomorphism.
* `MMP.Analytic.hypercohomologySingleIso`: the shift identification
  `ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)`, natural in `G`.
* `MMP.Analytic.hypercohomologyComparison_single`: on one-term complexes `F[-p]` the comparison
  is `MMP.Analytic.comparisonMap` in degree `n - p` under `hypercohomologySingleIso`.
* `MMP.Analytic.isIso_hypercohomologyPullback_comp_map_of_isProjective`: the two together.

## Implementation notes

The algebraic complex is `CochainComplex.of` of the abelian sheaves underlying the `F p`, with
`ℂ`-linearity of `δ^p` stated on sections, the scalar `c ∈ ℂ` acting through
`ℂ → Γ(X, U)`. The compatibility `δ^{p,an} ∘ ι_{F p} = ι_{F (p+1)} ∘ α_X⁻¹ δ^p` is recorded as
a morphism of complexes `ι` whose components are `MMP.Analytic.analytifyModuleι`. The bounds
of the complex are arbitrary integers `a ≤ … ≤ b`. The graded-piece assertion is stated for
the one-term complex `(HomologicalComplex.single _ _ p).obj G`, which is the graded piece
`σ_{≥ p} / σ_{≥ p+1}` of the stupid filtration.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §12
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace MMP.Analytic

open Analytification

section RowIso

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [B.HasTotal (ComplexShape.up ℤ)] (p : ℤ)

private lemma π_up (a b : ℤ) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) =
      a + b := rfl

/-- The inclusion of the row `p` of a bicomplex, shifted by `-p`, into its total complex. -/
private noncomputable def rowToTotal (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-p)).obj (B.X p) ⟶
      B.total (ComplexShape.up ℤ) where
  f i := B.ιTotal (ComplexShape.up ℤ) p (i + -p) i (by rw [π_up]; omega)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    have h1 : IsZero ((B.X (p + 1)).X (i + -p)) :=
      (HomologicalComplex.eval _ _ _).map_isZero (hB _ (by omega))
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)
        _ _ (by rw [π_up]; omega),
      HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (i + -p) (j + -p) by
        change i + -p + 1 = j + -p; omega) _ (by rw [π_up]; omega)]
    rw [h1.eq_of_tgt ((B.d p (p + 1)).f (i + -p)) 0]
    simp [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg]

private lemma isIso_rowToTotal (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) :
    IsIso (rowToTotal B p hB) := by
  suffices h : ∀ i, IsIso ((rowToTotal B p hB).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  refine ⟨B.totalDesc (fun i₁ i₂ h => if h₁ : i₁ = p then
    (B.XXIsoOfEq _ _ _ h₁ (show i₂ = i + -p by
      have h' : i₁ + i₂ = i := h
      omega)).hom
      else 0), ?_, ?_⟩
  · simp [rowToTotal]
  · refine HomologicalComplex₂.total.hom_ext _ fun i₁ i₂ h => ?_
    by_cases h₁ : i₁ = p
    · subst h₁
      have h₂ : i₂ = i + -i₁ := by
        have h' : i₁ + i₂ = i := h
        omega
      subst h₂
      simp [rowToTotal]
    · exact ((HomologicalComplex.eval _ _ i₂).map_isZero (hB _ h₁)).eq_of_src _ _

private lemma rowToTotal_naturality
    {B B' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [B.HasTotal (ComplexShape.up ℤ)] [B'.HasTotal (ComplexShape.up ℤ)]
    (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (hB' : ∀ q : ℤ, q ≠ p → IsZero (B'.X q))
    (φ : B ⟶ B') :
    rowToTotal B p hB ≫ HomologicalComplex₂.total.map φ (ComplexShape.up ℤ) =
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-p)).map (φ.f p) ≫
        rowToTotal B' p hB' := by
  ext i : 1
  simp [rowToTotal]

end RowIso

section RowHomology

variable {C : Type*} [Category C] [Abelian C]
  (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [B.HasTotal (ComplexShape.up ℤ)] (p : ℤ)

/-- `H^n(K⟦x⟧) ≅ H^m(K)` for `x + n = m`. -/
private noncomputable def shiftHomologyIso (K : CochainComplex C ℤ) (x n m : ℤ)
    (h : x + n = m) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) x).obj K).homology n ≅ K.homology m :=
  (CochainComplex.ShiftSequence.shiftIso C x n m h).app K

private lemma shiftHomologyIso_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (x n m : ℤ) (h : x + n = m) :
    HomologicalComplex.homologyMap
        ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) x).map φ) n ≫
      (shiftHomologyIso L x n m h).hom =
    (shiftHomologyIso K x n m h).hom ≫ HomologicalComplex.homologyMap φ m :=
  (CochainComplex.ShiftSequence.shiftIso C x n m h).hom.naturality φ

/-- The cohomology of a bicomplex concentrated in the row `p`: `H^n(Tot B) ≅ H^m(B^{p,•})` for
`-p + n = m`. -/
private noncomputable def rowHomologyIso (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (n m : ℤ)
    (h : -p + n = m) :
    (B.total (ComplexShape.up ℤ)).homology n ≅ (B.X p).homology m :=
  haveI := isIso_rowToTotal B p hB
  (asIso (HomologicalComplex.homologyMap (rowToTotal B p hB) n)).symm ≪≫
    shiftHomologyIso (B.X p) (-p) n m h

private lemma rowHomologyIso_naturality
    {B B' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [B.HasTotal (ComplexShape.up ℤ)] [B'.HasTotal (ComplexShape.up ℤ)]
    (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (hB' : ∀ q : ℤ, q ≠ p → IsZero (B'.X q))
    (φ : B ⟶ B') (n m : ℤ) (h : -p + n = m) :
    (rowHomologyIso B p hB n m h).hom ≫ HomologicalComplex.homologyMap (φ.f p) m =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) n ≫
        (rowHomologyIso B' p hB' n m h).hom := by
  haveI := isIso_rowToTotal B p hB
  haveI := isIso_rowToTotal B' p hB'
  have h2 := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (rowToTotal_naturality p hB hB' φ)
  simp only [HomologicalComplex.homologyMap_comp] at h2
  simp only [rowHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom,
    Category.assoc]
  rw [← cancel_epi (HomologicalComplex.homologyMap (rowToTotal B p hB) n),
    IsIso.hom_inv_id_assoc, reassoc_of% h2, IsIso.hom_inv_id_assoc]
  exact (shiftHomologyIso_naturality (φ.f p) (-p) n m h).symm

end RowHomology

section Truncation

variable {C : Type*} [Category C] [Abelian C] [HasZeroObject C] (K : CochainComplex C ℤ) (a : ℤ)
  (hK : ∀ i, i < a → IsZero (K.X i))

/-- The projection of a complex concentrated in degrees `≥ a` onto its term in degree `a`. -/
private noncomputable def projToSingle :
    K ⟶ (HomologicalComplex.single C _ a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i + 1 = a := hi
    exact (hK i (by omega)).eq_of_src _ _)

private lemma projToSingle_f :
    (projToSingle K a hK).f a =
      (HomologicalComplex.singleObjXSelf _ a (K.X a)).inv := by
  rw [projToSingle, HomologicalComplex.mkHomToSingle_f, Category.id_comp]

private lemma epi_projToSingle : Epi (projToSingle K a hK) := by
  refine HomologicalComplex.epi_of_epi_f _ fun i => ?_
  by_cases hi : i = a
  · subst hi
    rw [projToSingle_f]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _

/-- The stupid filtration step `0 → σ_{> a} K → K → K^a[-a] → 0`. -/
private noncomputable abbrev truncSeq : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι (projToSingle K a hK)) (projToSingle K a hK) (kernel.condition _)

private lemma truncSeq_shortExact : (truncSeq K a hK).ShortExact := by
  have := epi_projToSingle K a hK
  exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

private lemma truncSeq_eval_shortExact (i : ℤ) :
    ((truncSeq K a hK).map (HomologicalComplex.eval _ _ i)).ShortExact :=
  (truncSeq_shortExact K a hK).map_of_exact _

private lemma isZero_truncSeq_X₁ (i : ℤ) (hi : i ≤ a ∨ IsZero (K.X i)) :
    IsZero ((truncSeq K a hK).X₁.X i) := by
  have hS := truncSeq_eval_shortExact K a hK i
  rcases hi with hi | hi
  · rcases lt_or_eq_of_le hi with hi | rfl
    · have := hS.mono_f
      exact IsZero.of_mono ((kernel.ι (projToSingle K a hK)).f i) (hK i hi)
    · refine hS.isIso_g_iff.1 ?_
      change IsIso ((projToSingle K i hK).f i)
      rw [projToSingle_f]
      infer_instance
  · have := hS.mono_f
    exact IsZero.of_mono ((kernel.ι (projToSingle K a hK)).f i) hi

private lemma isIso_truncSeq_f (i : ℤ) (hi : i ≠ a) :
    IsIso ((kernel.ι (projToSingle K a hK)).f i) :=
  (truncSeq_eval_shortExact K a hK i).isIso_f_iff.2
    (HomologicalComplex.isZero_single_obj_X (c := ComplexShape.up ℤ) _ _ _ hi)

/-- If `K` is supported in `[a, a + (m + 1)]`, then `σ_{> a} K` is supported in
`[a + 1, a + 1 + m]`. -/
private lemma isZero_truncSeq_X₁_of_bounded (m : ℕ)
    (hb : ∀ i, i < a ∨ a + (m + 1 : ℕ) < i → IsZero (K.X i)) :
    ∀ i, i < a + 1 ∨ a + 1 + m < i → IsZero ((truncSeq K a hK).X₁.X i) := by
  intro i hi
  refine isZero_truncSeq_X₁ K a hK i ?_
  rcases hi with hi | hi
  · exact Or.inl (by omega)
  · exact Or.inr (hb i (Or.inr (by push_cast; omega)))

/-- The three terms of the stupid filtration step of a complex supported in
`[a, a + (m + 1)]` are all supported in that interval. -/
private lemma truncSeq_bounded (m : ℕ)
    (hb : ∀ i, i < a ∨ a + (m + 1 : ℕ) < i → IsZero (K.X i)) :
    ∃ a' b' : ℤ, (truncSeq K a hK).X₁.IsStrictlyGE a' ∧
      (truncSeq K a hK).X₁.IsStrictlyLE b' ∧ (truncSeq K a hK).X₂.IsStrictlyGE a' ∧
      (truncSeq K a hK).X₂.IsStrictlyLE b' ∧ (truncSeq K a hK).X₃.IsStrictlyGE a' ∧
      (truncSeq K a hK).X₃.IsStrictlyLE b' :=
  have h₁ := isZero_truncSeq_X₁_of_bounded K a hK m hb
  have h₃ : ∀ i, i ≠ a → IsZero ((truncSeq K a hK).X₃.X i) :=
    fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  ⟨a, a + (m + 1 : ℕ),
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => h₁ i (Or.inl (by omega)),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => h₁ i (Or.inr (by push_cast at hi ⊢; omega)),
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => hb i (Or.inl hi),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => hb i (Or.inr hi),
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => h₃ i (by omega),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => h₃ i (by push_cast at hi; omega)⟩

end Truncation

section FiveLemma

open ComposableArrows Abelian HomologicalComplex.HomologySequence

variable {C : Type*} [Category C] [Abelian C] {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
  (φ : S₁ ⟶ S₂)

/-- The five lemma on the long exact homology sequences: a morphism of short exact sequences of
cochain complexes which is an isomorphism in cohomology on the outer terms is one on the middle
term. -/
private lemma isIso_homologyMap_τ₂ (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : ∀ n, IsIso (HomologicalComplex.homologyMap φ.τ₁ n))
    (h₃ : ∀ n, IsIso (HomologicalComplex.homologyMap φ.τ₃ n)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap φ.τ₂ n) := by
  have hm : Mono (HomologicalComplex.homologyMap φ.τ₂ n) := by
    have hr : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
    exact mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ (n - 1) n hr))
      (composableArrows₅_exact hS₁ (n - 1) n hr).δ₀.δ₀
      (composableArrows₅_exact hS₂ (n - 1) n hr).δ₀.δ₀
      (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₃ (n - 1)))
      (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₁ n))
      (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₃ n))
  have he : Epi (HomologicalComplex.homologyMap φ.τ₂ n) := by
    have hr : (ComplexShape.up ℤ).Rel n (n + 1) := by simp
    exact epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ n (n + 1) hr))
      (composableArrows₅_exact hS₁ n (n + 1) hr).δlast.δlast
      (composableArrows₅_exact hS₂ n (n + 1) hr).δlast.δlast
      (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₁ n))
      (inferInstance : Epi (HomologicalComplex.homologyMap φ.τ₃ n))
      (inferInstance : Mono (HomologicalComplex.homologyMap φ.τ₁ (n + 1)))
  exact isIso_of_mono_of_epi _

end FiveLemma

section Godement

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- The comparison `Γ(T, G^•(G)) ⟶ Γ(T', G^•(G'))` of Godement sections induced by
`θ : f⁻¹ G ⟶ G'`. -/
private noncomputable def gsComparison {G : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G') :
    (godementSections T).obj G ⟶ (godementSections T').obj G' :=
  godementSectionsPullback f G ≫ (godementSections T').map θ

private lemma hypercohomology_map_heq {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (φ : K ⟶ L) (n : ℤ) :
    HEq ((hypercohomology T n).map φ) (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map φ) (ComplexShape.up ℤ)) n) := HEq.rfl

private lemma hypercohomologyPullback_heq (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (n : ℤ) :
    HEq (hypercohomologyPullback f K n) (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
        (ComplexShape.up ℤ)) n) := HEq.rfl

/-- The hypercohomology of a complex concentrated in degree `p`: `ℍ^n(T, K) ≅ H^m(Γ(T, G^•K^p))`
for `-p + n = m`. -/
private noncomputable def hyperRowIso (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (p : ℤ) (hK : ∀ i, i ≠ p → IsZero (K.X i)) (n m : ℤ) (h : -p + n = m) :
    (hypercohomology T n).obj K ≅ ((godementSectionsDoubleComplex T K).X p).homology m :=
  eqToIso (hypercohomology_obj T n K) ≪≫
    rowHomologyIso _ p (fun q hq => (godementSections T).map_isZero (hK q hq)) n m h

private lemma hyperRowIso_naturality {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (φ : K ⟶ L) (p : ℤ) (hK : ∀ i, i ≠ p → IsZero (K.X i)) (hL : ∀ i, i ≠ p → IsZero (L.X i))
    (n m : ℤ) (h : -p + n = m) :
    (hyperRowIso K p hK n m h).hom ≫
        HomologicalComplex.homologyMap
          ((((godementSections T).mapHomologicalComplex _).map φ).f p) m =
      (hypercohomology T n).map φ ≫ (hyperRowIso L p hL n m h).hom := by
  have e := (conj_eqToHom_iff_heq _ _ (hypercohomology_obj T n K)
    (hypercohomology_obj T n L)).2 (hypercohomology_map_heq φ n)
  simp only [hyperRowIso, Iso.trans_hom, eqToIso.hom, Category.assoc, e, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  congr 1
  exact rowHomologyIso_naturality p _ _ _ n m h

private lemma hyperRowIso_pullback (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (p : ℤ) (hK : ∀ i, i ≠ p → IsZero (K.X i))
    (hK' : ∀ i, i ≠ p → IsZero (((complexPullback f).obj K).X i))
    (n m : ℤ) (h : -p + n = m) :
    (hyperRowIso K p hK n m h).hom ≫
        HomologicalComplex.homologyMap (godementSectionsPullback f (K.X p)) m =
      hypercohomologyPullback f K n ≫ (hyperRowIso _ p hK' n m h).hom := by
  have e := (conj_eqToHom_iff_heq _ _ (hypercohomology_obj T n K)
    (hypercohomology_obj T' n ((complexPullback f).obj K))).2 (hypercohomologyPullback_heq f K n)
  simp only [hyperRowIso, Iso.trans_hom, eqToIso.hom, Category.assoc, e, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  congr 1
  exact rowHomologyIso_naturality p _ _ (godementSectionsDoubleComplexPullback f K) n m h

/-- For complexes concentrated in degree `p`, the comparison on hypercohomology is the comparison
of Godement sections in degree `p`, shifted. -/
private lemma hyperComparison_eq
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (p : ℤ)
    (hK : ∀ i, i ≠ p → IsZero (K.X i)) (hK' : ∀ i, i ≠ p → IsZero (((complexPullback f).obj K).X i))
    (hL : ∀ i, i ≠ p → IsZero (L.X i))
    (n m : ℤ) (h : -p + n = m) :
    (hyperRowIso K p hK n m h).hom ≫
        HomologicalComplex.homologyMap (gsComparison f (ι.f p)) m =
      (hypercohomologyPullback f K n ≫ (hypercohomology T' n).map ι) ≫
        (hyperRowIso L p hL n m h).hom := by
  rw [gsComparison, HomologicalComplex.homologyMap_comp, reassoc_of% (hyperRowIso_pullback f K p
    hK hK' n m h), Category.assoc]
  congr 1
  exact hyperRowIso_naturality ι p hK' hL n m h

private lemma gsComparison_comp_map {G G₁ : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' G'₁ : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G')
    (θ₁ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G₁ ⟶ G'₁) (u : G ⟶ G₁) (v : G' ⟶ G'₁)
    (hθ : θ ≫ v = (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map u ≫ θ₁) :
    gsComparison f θ ≫ (godementSections T').map v =
      (godementSections T).map u ≫ gsComparison f θ₁ := by
  simp only [gsComparison, Category.assoc, ← Functor.map_comp, hθ,
    godementSections_map_comp_godementSectionsPullback_assoc]

/-- Transport of the invertibility of a comparison along isomorphisms. -/
private lemma isIso_gsComparison_iff {G G₁ : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' G'₁ : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G')
    (θ₁ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G₁ ⟶ G'₁) (u : G ⟶ G₁) (v : G' ⟶ G'₁)
    [IsIso u] [IsIso v]
    (hθ : θ ≫ v = (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map u ≫ θ₁) (q : ℤ) :
    IsIso (HomologicalComplex.homologyMap (gsComparison f θ) q) ↔
      IsIso (HomologicalComplex.homologyMap (gsComparison f θ₁) q) := by
  rw [← isIso_comp_right_iff _ (HomologicalComplex.homologyMap ((godementSections T').map v) q),
    ← HomologicalComplex.homologyMap_comp, gsComparison_comp_map f θ θ₁ u v hθ,
    HomologicalComplex.homologyMap_comp, isIso_comp_left_iff]

/-- The comparison between zero sheaves is an isomorphism. -/
private lemma isIso_gsComparison_of_isZero {G : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G') (hG : IsZero G)
    (hG' : IsZero G') (q : ℤ) :
    IsIso (HomologicalComplex.homologyMap (gsComparison f θ) q) :=
  isIso_of_source_target_iso_zero _
    ((godementSections T ⋙ HomologicalComplex.homologyFunctor _ _ q).map_isZero hG).isoZero
    ((godementSections T' ⋙ HomologicalComplex.homologyFunctor _ _ q).map_isZero hG').isoZero

/-- The one-term case: for complexes concentrated in degree `p`, the comparison on hypercohomology
is an isomorphism once the comparison of Godement sections of the degree `p` terms is. -/
private lemma isIso_hyperComparison_of_single
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (p : ℤ)
    (hK : ∀ i, i ≠ p → IsZero (K.X i)) (hL : ∀ i, i ≠ p → IsZero (L.X i))
    (hγ : ∀ q, IsIso (HomologicalComplex.homologyMap (gsComparison f (ι.f p)) q)) (n : ℤ) :
    IsIso (hypercohomologyPullback f K n ≫ (hypercohomology T' n).map ι) := by
  have hK' : ∀ i, i ≠ p → IsZero (((complexPullback f).obj K).X i) :=
    fun i hi => (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map_isZero (hK i hi)
  rw [(Iso.eq_comp_inv _).2 (hyperComparison_eq f ι p hK hK' hL n (-p + n) rfl).symm]
  infer_instance

/-- The comparison on total complexes of Godement sections induced by `ι : f⁻¹ K ⟶ L`. -/
private noncomputable def totalComparison
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) :
    (godementSectionsDoubleComplex T K).total (ComplexShape.up ℤ) ⟶
      (godementSectionsDoubleComplex T' L).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K) (ComplexShape.up ℤ) ≫
    HomologicalComplex₂.total.map (((godementSections T').mapHomologicalComplex _).map ι)
      (ComplexShape.up ℤ)

/-- The comparison on hypercohomology, written on total complexes of Godement sections. -/
private noncomputable def homologyComparison
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (n : ℤ) :
    ((godementSectionsDoubleComplex T K).total (ComplexShape.up ℤ)).homology n ⟶
      ((godementSectionsDoubleComplex T' L).total (ComplexShape.up ℤ)).homology n :=
  HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (godementSectionsDoubleComplexPullback f K) (ComplexShape.up ℤ)) n ≫
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (((godementSections T').mapHomologicalComplex _).map ι) (ComplexShape.up ℤ)) n

private lemma homologyComparison_eq
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (n : ℤ) :
    homologyComparison f ι n = HomologicalComplex.homologyMap (totalComparison f ι) n := by
  rw [homologyComparison, totalComparison, HomologicalComplex.homologyMap_comp]

private lemma isIso_homologyComparison_iff
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (n : ℤ) :
    IsIso (homologyComparison f ι n) ↔
      IsIso (hypercohomologyPullback f K n ≫ (hypercohomology T' n).map ι) :=
  Iff.rfl

private lemma godementSectionsDoubleComplexPullback_naturality
    {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ K') :
    ((godementSections T).mapHomologicalComplex _).map φ ≫
        godementSectionsDoubleComplexPullback f K' =
      godementSectionsDoubleComplexPullback f K ≫
        ((godementSections T').mapHomologicalComplex _).map ((complexPullback f).map φ) := by
  ext q : 1
  exact godementSections_map_comp_godementSectionsPullback f (φ.f q)

private lemma totalComparison_naturality
    {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L L' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (ι' : (complexPullback f).obj K' ⟶ L')
    (φ : K ⟶ K') (ψ : L ⟶ L') (comm : (complexPullback f).map φ ≫ ι' = ι ≫ ψ) :
    totalComparison f ι ≫ HomologicalComplex₂.total.map
        (((godementSections T').mapHomologicalComplex _).map ψ) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map φ) (ComplexShape.up ℤ) ≫
        totalComparison f ι' := by
  simp only [totalComparison, ← HomologicalComplex₂.total.map_comp, ← Category.assoc,
    godementSectionsDoubleComplexPullback_naturality]
  simp only [Category.assoc, ← Functor.map_comp, comm]

/-- The five lemma step: for a degreewise short exact sequence of bounded complexes on `T`, a
degreewise short exact sequence of bounded complexes on `T'` and maps `τᵢ` from the inverse image
of the first to the second commuting with the differentials, the comparison is an isomorphism on
the middle terms once it is on the outer ones. -/
private lemma isIso_homologyComparison_of_shortExact
    (S : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ))
    (S' : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ))
    (τ₁ : (complexPullback f).obj S.X₁ ⟶ S'.X₁) (τ₂ : (complexPullback f).obj S.X₂ ⟶ S'.X₂)
    (τ₃ : (complexPullback f).obj S.X₃ ⟶ S'.X₃)
    (c₁₂ : (complexPullback f).map S.f ≫ τ₂ = τ₁ ≫ S'.f)
    (c₂₃ : (complexPullback f).map S.g ≫ τ₃ = τ₂ ≫ S'.g)
    (hS : ∀ i : ℤ, (S.map (HomologicalComplex.eval _ _ i)).ShortExact)
    (hS' : ∀ i : ℤ, (S'.map (HomologicalComplex.eval _ _ i)).ShortExact)
    (hb : ∃ a b : ℤ, S.X₁.IsStrictlyGE a ∧ S.X₁.IsStrictlyLE b ∧ S.X₂.IsStrictlyGE a ∧
      S.X₂.IsStrictlyLE b ∧ S.X₃.IsStrictlyGE a ∧ S.X₃.IsStrictlyLE b)
    (hb' : ∃ a b : ℤ, S'.X₁.IsStrictlyGE a ∧ S'.X₁.IsStrictlyLE b ∧ S'.X₂.IsStrictlyGE a ∧
      S'.X₂.IsStrictlyLE b ∧ S'.X₃.IsStrictlyGE a ∧ S'.X₃.IsStrictlyLE b)
    (h₁ : ∀ n, IsIso (homologyComparison f τ₁ n))
    (h₃ : ∀ n, IsIso (homologyComparison f τ₃ n)) (n : ℤ) :
    IsIso (homologyComparison f τ₂ n) := by
  obtain ⟨hT, -⟩ := (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).2.2.1.2.1 S hS hb
  obtain ⟨hT', -⟩ := (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T').2.2.1.2.1 S' hS' hb'
  have key := fun φ => isIso_homologyMap_τ₂ φ hT hT'
  rw [homologyComparison_eq]
  refine key ⟨totalComparison f τ₁, totalComparison f τ₂, totalComparison f τ₃,
    totalComparison_naturality f τ₁ τ₂ S.f S'.f c₁₂,
    totalComparison_naturality f τ₂ τ₃ S.g S'.g c₂₃⟩
    (fun n => by rw [← homologyComparison_eq]; exact h₁ n)
    (fun n => by rw [← homologyComparison_eq]; exact h₃ n) n

/-- A lift `τ` of `ι` to the kernels of the projections to degree `a` induces isomorphisms of
Godement sections in every degree once `ι` does and the kernels vanish in degree `a`. -/
private lemma isIso_gsComparison_truncSeq_X₁
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (ι : (complexPullback f).obj K ⟶ L) (a : ℤ) (hKa : ∀ i, i < a → IsZero (K.X i))
    (hLa : ∀ i, i < a → IsZero (L.X i))
    (τ : (complexPullback f).obj (truncSeq K a hKa).X₁ ⟶ (truncSeq L a hLa).X₁)
    (hτ : τ ≫ (truncSeq L a hLa).f = (complexPullback f).map (truncSeq K a hKa).f ≫ ι)
    (hK₁ : IsZero ((truncSeq K a hKa).X₁.X a)) (hL₁ : IsZero ((truncSeq L a hLa).X₁.X a))
    (hγ : ∀ p q, IsIso (HomologicalComplex.homologyMap (gsComparison f (ι.f p)) q)) (p q : ℤ) :
    IsIso (HomologicalComplex.homologyMap (gsComparison f (τ.f p)) q) := by
  by_cases hp : p = a
  · subst hp
    exact isIso_gsComparison_of_isZero f _ hK₁ hL₁ q
  · have : IsIso ((truncSeq K a hKa).f.f p) := isIso_truncSeq_f K a hKa p hp
    have : IsIso ((truncSeq L a hLa).f.f p) := isIso_truncSeq_f L a hLa p hp
    have h : τ.f p ≫ (truncSeq L a hLa).f.f p =
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map ((truncSeq K a hKa).f.f p) ≫ ι.f p :=
      HomologicalComplex.congr_hom hτ p
    exact (isIso_gsComparison_iff f _ _ _ _ h q).2 (hγ p q)

/-- The hypercohomology comparison for complexes supported in `[a, a + m]`, by induction on `m`
along the stupid filtration and the five lemma. -/
private lemma isIso_homologyComparison_of_bounded (m : ℕ) :
    ∀ (a : ℤ) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
      (L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ)
      (ι : (complexPullback f).obj K ⟶ L),
      (∀ i, i < a ∨ a + m < i → IsZero (K.X i)) → (∀ i, i < a ∨ a + m < i → IsZero (L.X i)) →
      (∀ p q, IsIso (HomologicalComplex.homologyMap (gsComparison f (ι.f p)) q)) →
      ∀ n, IsIso (homologyComparison f ι n) := by
  induction m with
  | zero =>
    intro a K L ι hK hL hγ n
    exact (isIso_homologyComparison_iff f ι n).2 (isIso_hyperComparison_of_single f ι a
      (fun i hi => hK i (by omega)) (fun i hi => hL i (by omega)) (hγ a) n)
  | succ m ih =>
    intro a K L ι hK hL hγ n
    have hKa : ∀ i, i < a → IsZero (K.X i) := fun i hi => hK i (Or.inl hi)
    have hLa : ∀ i, i < a → IsZero (L.X i) := fun i hi => hL i (Or.inl hi)
    set πK := projToSingle K a hKa
    set πL := projToSingle L a hLa
    let τ₃ : (complexPullback f).obj (truncSeq K a hKa).X₃ ⟶ (truncSeq L a hLa).X₃ :=
      (HomologicalComplex.singleMapHomologicalComplex
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) _ a).hom.app (K.X a) ≫
        (HomologicalComplex.single _ _ a).map (ι.f a)
    have hτ₃ : τ₃.f a ≫ (HomologicalComplex.singleObjXSelf _ a (L.X a)).hom =
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map
          (HomologicalComplex.singleObjXSelf _ a (K.X a)).hom ≫ ι.f a := by
      simp [τ₃, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
    have hcomm₂₃ : ι ≫ πL = (complexPullback f).map πK ≫ τ₃ := by
      refine HomologicalComplex.to_single_hom_ext ?_
      rw [← cancel_mono (HomologicalComplex.singleObjXSelf _ a (L.X a)).hom]
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
        hτ₃, πK, πL, ← Functor.map_comp_assoc]
      rw [projToSingle_f, projToSingle_f]
      simp
    let τ₁ : (complexPullback f).obj (truncSeq K a hKa).X₁ ⟶ (truncSeq L a hLa).X₁ :=
      kernel.lift πL ((complexPullback f).map (truncSeq K a hKa).f ≫ ι) (by
        rw [Category.assoc, hcomm₂₃, ← Functor.map_comp_assoc, (truncSeq K a hKa).zero,
          Functor.map_zero, zero_comp])
    have hcomm₁₂ : τ₁ ≫ (truncSeq L a hLa).f =
        (complexPullback f).map (truncSeq K a hKa).f ≫ ι :=
      kernel.lift_ι _ _ _
    have hK₁ := isZero_truncSeq_X₁_of_bounded K a hKa m hK
    have hL₁ := isZero_truncSeq_X₁_of_bounded L a hLa m hL
    have hγ₁ := isIso_gsComparison_truncSeq_X₁ f ι a hKa hLa τ₁ hcomm₁₂
      (hK₁ a (Or.inl (by omega))) (hL₁ a (Or.inl (by omega))) hγ
    have hγ₃ : ∀ q, IsIso (HomologicalComplex.homologyMap (gsComparison f (τ₃.f a)) q) :=
      fun q => (isIso_gsComparison_iff f _ _ _ _ hτ₃ q).2 (hγ a q)
    have h₁ := ih (a + 1) _ _ τ₁ hK₁ hL₁ hγ₁
    have h₃ : ∀ n, IsIso (homologyComparison f τ₃ n) := fun n =>
      (isIso_homologyComparison_iff f τ₃ n).2
        (isIso_hyperComparison_of_single f τ₃ a
          (fun _ hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
          (fun _ hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) hγ₃ n)
    refine isIso_homologyComparison_of_shortExact f (truncSeq K a hKa) (truncSeq L a hLa) τ₁ ι τ₃
      ?_ ?_ (truncSeq_eval_shortExact K a hKa) (truncSeq_eval_shortExact L a hLa)
      (truncSeq_bounded K a hKa m hK) (truncSeq_bounded L a hLa m hL) ?_ ?_ n
    · exact hcomm₁₂.symm
    · exact hcomm₂₃.symm
    · exact h₁
    · exact h₃

/-- The component at `G` of `singleHyperIso`. -/
private noncomputable def singleHyperIsoApp (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (hypercohomology T n).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) ≅
      ((godementSections T).obj G).homology m :=
  hyperRowIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) p
      (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h ≪≫
    (HomologicalComplex.homologyFunctor _ _ m).mapIso
      ((godementSections T).mapIso (HomologicalComplex.singleObjXSelf _ p G))

private lemma singleHyperIsoApp_hom (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (singleHyperIsoApp T p n m h G).hom =
      (hyperRowIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) p
          (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h).hom ≫
        HomologicalComplex.homologyMap
          ((godementSections T).map (HomologicalComplex.singleObjXSelf _ p G).hom) m :=
  rfl

private lemma singleHyperIsoApp_naturality (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    {G G' : TopCat.Sheaf AddCommGrpCat.{u} T} (g : G ⟶ G') :
    (hypercohomology T n).map ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).map g) ≫
        (singleHyperIsoApp T p n m h G').hom =
      (singleHyperIsoApp T p n m h G).hom ≫
        HomologicalComplex.homologyMap ((godementSections T).map g) m := by
  have e := hyperRowIso_naturality ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).map g)
    p (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h
  rw [singleHyperIsoApp_hom, singleHyperIsoApp_hom, ← reassoc_of% e, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp,
    HomologicalComplex.single_map_f_self]
  simp

/-- The hypercohomology of the one-term complex `G[-p]`: `ℍ^n(T, G[-p]) ≅ H^m(Γ(T, G^•G))` for
`-p + n = m`, naturally in `G`. -/
private noncomputable def singleHyperIso (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m) :
    HomologicalComplex.single _ (ComplexShape.up ℤ) p ⋙ hypercohomology T n ≅
      godementSections T ⋙ HomologicalComplex.homologyFunctor _ _ m :=
  NatIso.ofComponents (singleHyperIsoApp T p n m h)
    (fun g => singleHyperIsoApp_naturality T p n m h g)

/-- The comparison on the one-term complexes `G[-p]`, `G'[-p]` induced by `θ : f⁻¹ G ⟶ G'` is the
comparison of Godement sections. -/
private lemma singleHyperIso_comparison {G : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G') (p n m : ℤ) (h : -p + n = m) :
    (hypercohomologyPullback f ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) n ≫
        (hypercohomology T' n).map
          ((HomologicalComplex.singleMapHomologicalComplex
              (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) p).hom.app G ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) p).map θ)) ≫
        (singleHyperIsoApp T' p n m h G').hom =
      (singleHyperIsoApp T p n m h G).hom ≫
        HomologicalComplex.homologyMap (gsComparison f θ) m := by
  set ι' := (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) p).hom.app G ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) p).map θ
  have hsq : ι'.f p ≫ (HomologicalComplex.singleObjXSelf _ p G').hom =
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map
        (HomologicalComplex.singleObjXSelf _ p G).hom ≫ θ := by
    simp [ι', HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
  have e := hyperComparison_eq f ι' p
    (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    (fun i hi => (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi))
    (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h
  have e₂ := congrArg (fun g => HomologicalComplex.homologyMap g m)
    (gsComparison_comp_map f _ _ _ _ hsq)
  simp only [HomologicalComplex.homologyMap_comp] at e₂
  rw [singleHyperIsoApp_hom, singleHyperIsoApp_hom]
  simp only [Category.assoc] at e ⊢
  rw [← reassoc_of% e, e₂]

private lemma neg_zero_add (m : ℤ) : -0 + m = m := by omega

/-- Under `singleHyperIso T p n m h ≪≫ (singleHyperIso T 0 m m _).symm`, the comparison on `ℍ^n`
of one-term complexes in degree `p` is any map on `H^m` which corresponds to the comparison of
Godement sections. -/
private lemma singleHyperShift_comparison {G : TopCat.Sheaf AddCommGrpCat.{u} T}
    {G' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G') (p n m : ℤ) (h : -p + n = m)
    (c : (sheafCohomology T m).obj G ⟶ (sheafCohomology T' m).obj G')
    (hcomp : c ≫ (singleHyperIsoApp T' 0 m m (neg_zero_add m) G').hom =
      (singleHyperIsoApp T 0 m m (neg_zero_add m) G).hom ≫
        HomologicalComplex.homologyMap (gsComparison f θ) m) :
    (hypercohomologyPullback f _ n ≫
        (hypercohomology T' n).map
          ((HomologicalComplex.singleMapHomologicalComplex
              (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) p).hom.app G ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) p).map θ)) ≫
        ((singleHyperIsoApp T' p n m h G').hom ≫
          (singleHyperIsoApp T' 0 m m (neg_zero_add m) G').inv) =
      ((singleHyperIsoApp T p n m h G).hom ≫
          (singleHyperIsoApp T 0 m m (neg_zero_add m) G).inv) ≫ c := by
  rw [← Category.assoc, singleHyperIso_comparison f θ p n m h, Category.assoc]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  congr 1
  exact (Iso.eq_inv_comp _).2
    ((Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).2 hcomp.symm))

end Godement

/-- `comparisonMap` is the hypercohomology comparison of the one-term complexes in degree `0`. -/
private lemma comparisonMap_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (F : X.Modules) (q : ℤ) :
    comparisonMap sX F q = hypercohomologyPullback (toSchemeHom sX) _ q ≫
      (hypercohomology (space sX) q).map
        ((HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX))
            (ComplexShape.up ℤ) 0).hom.app ((SheafOfModules.toSheaf _).obj F) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (analytifyModuleι sX F)) := by
  rw [Functor.map_comp, ← Category.assoc]
  rfl

/-- The comparison of Godement sections of a coherent sheaf on a projective complex scheme is an
isomorphism in every degree. -/
private lemma isIso_gsComparison_analytifyModuleι {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) (F : X.Modules) (hF : Stacks.SheafOfModules.IsCoherent F) (q : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (gsComparison (toSchemeHom sX) (analytifyModuleι sX F)) q) := by
  have e := singleHyperIso_comparison (toSchemeHom sX) (analytifyModuleι sX F) 0 q q
    (neg_zero_add q)
  rw [← comparisonMap_eq] at e
  have := isIso_comparisonMap_of_isProjective sX hX F hF q
  rw [← isIso_comp_left_iff
    (singleHyperIsoApp _ 0 q q (neg_zero_add q) ((SheafOfModules.toSheaf _).obj F)).hom, ← e]
  exact IsIso.comp_isIso' this inferInstance

private lemma isZero_analytifyModule {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {F : X.Modules}
    (h : IsZero F) : IsZero ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F)) := by
  have : (analytifyModule sX).IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).isLeftAdjoint
  exact (SheafOfModules.toSheaf _).map_isZero (Functor.map_isZero _ h)

/-- The map `ℍ^n(X, K^•) → ℍ^n(X^an, L^•)` induced by a morphism of complexes
`ι : α_X⁻¹ K^• ⟶ L^•` of abelian sheaves on `X^an`: the Godement pullback along
`α_X : X^an → X` followed by `ι_*`. -/
noncomputable def hypercohomologyComparison {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X.toPresheafedSpace.carrier) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) ℤ}
    (ι : (complexPullback (toSchemeHom sX)).obj K ⟶ L) (n : ℤ) :
    (hypercohomology X.toPresheafedSpace.carrier n).obj K ⟶ (hypercohomology (space sX) n).obj L :=
  hypercohomologyPullback (toSchemeHom sX) K n ≫ (hypercohomology (space sX) n).map ι

/-- The morphism of one-term complexes `α_X⁻¹ (F[-p]) ⟶ F^an[-p]` with component
`analytifyModuleι sX F` in degree `p`. -/
noncomputable def singleAnalytifyModuleι {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (F : X.Modules) (p : ℤ) :
    (complexPullback (toSchemeHom sX)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj
          ((SheafOfModules.toSheaf _).obj F)) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj
        ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F)) :=
  (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)) (ComplexShape.up ℤ) p).hom.app
      ((SheafOfModules.toSheaf _).obj F) ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) p).map (analytifyModuleι sX F)

/-- **GAGA for hypercohomology, the isomorphism.** Let `X` be projective over `ℂ` and `K^•` a
bounded complex of coherent `𝒪_X`-modules `F p` with differentials `δ p`, and let `ι` be a morphism
of complexes `α_X⁻¹ K^• ⟶ K^{•,an}` whose components are `analytifyModuleι sX (F p)`. Then
`ι_* ∘ α_X^* : ℍ^n(X, K^•) → ℍ^n(X^an, K^{•,an})` is an isomorphism for every `n`. -/
public theorem isIso_hypercohomologyComparison_of_isProjective_of_bounded {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (F : ℤ → X.Modules)
    (hF : ∀ p, Stacks.SheafOfModules.IsCoherent (F p)) {a b : ℤ}
    (hb : ∀ p, p < a ∨ b < p → IsZero (F p))
    (δ : ∀ p, (SheafOfModules.toSheaf _).obj (F p) ⟶ (SheafOfModules.toSheaf _).obj (F (p + 1)))
    (hδ : ∀ p, δ p ≫ δ (p + 1) = 0)
    (δan : ∀ p, (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F (p + 1))))
    (hδan : ∀ p, δan p ≫ δan (p + 1) = 0)
    (ι : (complexPullback (toSchemeHom sX)).obj
        (CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj (F p)) δ hδ) ⟶
      CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)))
        δan hδan)
    (hι : ∀ p, ι.f p = analytifyModuleι sX (F p)) (n : ℤ) :
    IsIso (hypercohomologyComparison sX ι n) := by
  refine (isIso_homologyComparison_iff _ ι n).1 ?_
  refine isIso_homologyComparison_of_bounded (toSchemeHom sX) (b - a).toNat a _ _ ι
    (fun i hi => (SheafOfModules.toSheaf _).map_isZero (hb i (hi.imp_right fun h => by omega)))
    (fun i hi => isZero_analytifyModule sX (hb i (hi.imp_right fun h => by omega))) ?_ n
  intro p q
  rw [hι p]
  exact isIso_gsComparison_analytifyModuleι sX hX (F p) (hF p) q

end MMP.Analytic

end

/-! The identification `ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)` is built from the private row
isomorphisms above, so its body is not exposed. -/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace MMP.Analytic

open Analytification

/-- The identification `ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)` of the hypercohomology of the one-term
complex `G[-p]` (`G` placed in degree `p`) with sheaf cohomology, natural in `G`: the row
isomorphism of the Godement double complex of `G[-p]`, followed by the inverse of the one of
`G[0]`. -/
noncomputable def hypercohomologySingleIso (T : TopCat.{u}) (p n : ℤ) :
    HomologicalComplex.single _ (ComplexShape.up ℤ) p ⋙ hypercohomology T n ≅
      sheafCohomology T (n - p) :=
  singleHyperIso T p n (n - p) (neg_add_eq_sub p n) ≪≫
    (singleHyperIso T 0 (n - p) (n - p) (neg_zero_add _)).symm

/-- On the one-term complex `F[-p]`, the hypercohomology comparison `ℍ^n(X, F[-p]) →
ℍ^n(X^an, F^an[-p])` is the comparison map `c^{n-p}_F` under `hypercohomologySingleIso`. -/
theorem hypercohomologyComparison_single {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (F : X.Modules) (p n : ℤ) :
    hypercohomologyComparison sX (singleAnalytifyModuleι sX F p) n ≫
        (hypercohomologySingleIso (space sX) p n).hom.app
          ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F)) =
      (hypercohomologySingleIso X.toPresheafedSpace.carrier p n).hom.app
          ((SheafOfModules.toSheaf _).obj F) ≫ comparisonMap sX F (n - p) :=
  singleHyperShift_comparison (toSchemeHom sX) (analytifyModuleι sX F) p n (n - p)
    (neg_add_eq_sub p n) (comparisonMap sX F (n - p)) (by
      rw [comparisonMap_eq]
      exact singleHyperIso_comparison (toSchemeHom sX) (analytifyModuleι sX F) 0
        (n - p) (n - p) (neg_zero_add (n - p)))

/-- **GAGA for hypercohomology.** Let `X` be projective over `ℂ` and `K^•` a bounded complex of
coherent `𝒪_X`-modules `F p` with `ℂ`-linear differentials `δ p`, and let `ι` be a morphism of
complexes `α_X⁻¹ K^• ⟶ K^{•,an}` whose components are `analytifyModuleι sX (F p)`. Then
`ι_* ∘ α_X^* : ℍ^n(X, K^•) → ℍ^n(X^an, K^{•,an})` is an isomorphism for every `n`
(`isIso_hypercohomologyComparison_of_isProjective_of_bounded`); and for every `p` and `n`
the shift identifications `hypercohomologySingleIso : ℍ^n(T, G[-p]) ≅ H^{n-p}(T, G)` on `X` and on
`X^an` carry the map on the graded piece `(F p)[-p]` (`hypercohomologyComparison` of
`singleAnalytifyModuleι`) to `comparisonMap sX (F p) (n - p)` (`hypercohomologyComparison_single`).
-/
@[mmp "thm_mmp_gaga_projective_hypercohomology"]
theorem isIso_hypercohomologyPullback_comp_map_of_isProjective {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (F : ℤ → X.Modules)
    (hF : ∀ p, Stacks.SheafOfModules.IsCoherent (F p)) (a b : ℤ)
    (hb : ∀ p, p < a ∨ b < p → IsZero (F p))
    (δ : ∀ p, (SheafOfModules.toSheaf _).obj (F p) ⟶ (SheafOfModules.toSheaf _).obj (F (p + 1)))
    (hδℂ : ∀ (p : ℤ) (U : X.Opens) (c : ℂ) (s : (F p).val.obj (op U)),
      (δ p).hom.app (op U)
          ((show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) • s) =
        (show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) •
          (show (F (p + 1)).val.obj (op U) from (δ p).hom.app (op U) s))
    (hδ : ∀ p, δ p ≫ δ (p + 1) = 0)
    (δan : ∀ p, (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F (p + 1))))
    (hδan : ∀ p, δan p ≫ δan (p + 1) = 0)
    (ι : (complexPullback (toSchemeHom sX)).obj
        (CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj (F p)) δ hδ) ⟶
      CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p)))
        δan hδan)
    (hι : ∀ p, ι.f p = analytifyModuleι sX (F p)) :
    (∀ n : ℤ, IsIso (hypercohomologyPullback (toSchemeHom sX) _ n ≫
      (hypercohomology (space sX) n).map ι)) ∧
    ∀ p n : ℤ,
      hypercohomologyComparison sX (singleAnalytifyModuleι sX (F p) p) n ≫
          (hypercohomologySingleIso (space sX) p n).hom.app
            ((SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (F p))) =
        (hypercohomologySingleIso X.toPresheafedSpace.carrier p n).hom.app
            ((SheafOfModules.toSheaf _).obj (F p)) ≫ comparisonMap sX (F p) (n - p) :=
  ⟨isIso_hypercohomologyComparison_of_isProjective_of_bounded sX hX F hF hb δ hδ δan
      hδan ι hι,
    fun p n => hypercohomologyComparison_single sX (F p) p n⟩

end MMP.Analytic

end
