module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# An elementwise criterion for a quasi-isomorphism out of a cokernel

For a monomorphism `f : A ⟶ B` of complexes of modules and `g : B ⟶ D` with `f ≫ g = 0`, the
induced map `coker f ⟶ D` is a quasi-isomorphism once (S) every cycle `z` of `D` is, up to a
boundary, the image `g b` of a chain `b` of `B` whose differential lies in the image of `f`, and
(I) a chain `b` of `B` with differential in the image of `f` and `g b` a boundary is a boundary
up to the image of `f`. These are the two halves of the comparison of the relative homology
`H(B, A)` with `H(D)`. The criterion is also stated for complexes indexed by `ℕ` extended by zero
to `ℤ`.

## Main results

* `MMP.ModuleCatShortComplex.moduleCat_epi_homologyMap`,
  `MMP.ModuleCatShortComplex.moduleCat_mono_homologyMap`: elementwise surjectivity and
  injectivity of the map on homology of a map of short complexes of modules.
* `MMP.ModuleCatComplex.quasiIso_cokernelDesc_of_forall`: the criterion.
* `MMP.ModuleCatComplex.quasiIso_cokernelDesc_extendMap_of_forall`: the criterion for complexes
  extended from `ℕ` to `ℤ`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace MMP.ModuleCatShortComplex

open CategoryTheory CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

/-- An element `x` of `S.X₂` with `S.g x = 0` is the image of a cycle under `S.iCycles`. -/
lemma moduleCat_exists_iCycles_eq (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂)
    (hx : S.g x = 0) : ∃ c : S.cycles, S.iCycles c = x :=
  ⟨S.moduleCatCyclesIso.inv ⟨x, hx⟩, S.moduleCatCyclesIso_inv_iCycles_apply _⟩

/-- The image of a cycle under `S.iCycles` is killed by `S.g`. -/
lemma moduleCat_g_iCycles (S : ShortComplex (ModuleCat.{u} R)) (c : S.cycles) :
    S.g (S.iCycles c) = 0 := by
  rw [← ConcreteCategory.comp_apply, S.iCycles_g]; rfl

/-- A cycle whose class in homology vanishes is the image of an element of `S.X₁` under
`S.toCycles`. -/
lemma moduleCat_exists_toCycles_eq (S : ShortComplex (ModuleCat.{u} R)) (c : S.cycles)
    (hc : S.homologyπ c = 0) : ∃ y : S.X₁, S.toCycles y = c :=
  (ShortComplex.moduleCat_exact_iff _).1
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk S.toCycles S.homologyπ (by simp))
      S.homologyIsCokernel) c hc

/-- Surjectivity of the map on homology from an elementwise lifting of cycles up to
boundaries. -/
lemma moduleCat_epi_homologyMap {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (h : ∀ z : S₂.X₂, S₂.g z = 0 → ∃ k : S₁.X₂, S₁.g k = 0 ∧ ∃ e : S₂.X₁, φ.τ₂ k - z = S₂.f e) :
    Epi (homologyMap φ) := by
  rw [ModuleCat.epi_iff_surjective]
  intro a
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S₂.homologyπ).1 inferInstance a
  obtain ⟨k, hk, e, he⟩ := h _ (moduleCat_g_iCycles S₂ c)
  obtain ⟨c₁, hc₁⟩ := moduleCat_exists_iCycles_eq S₁ k hk
  refine ⟨S₁.homologyπ c₁, ?_⟩
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply,
    ← sub_eq_zero, ← map_sub]
  have : cyclesMap φ c₁ - c = S₂.toCycles e := by
    apply (ModuleCat.mono_iff_injective S₂.iCycles).1 inferInstance
    rw [map_sub, ← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hc₁,
      ← ConcreteCategory.comp_apply, toCycles_i, he]
  rw [this, ← ConcreteCategory.comp_apply, toCycles_comp_homologyπ]; rfl

/-- Injectivity of the map on homology from an elementwise condition. -/
lemma moduleCat_mono_homologyMap {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (h : ∀ k : S₁.X₂, S₁.g k = 0 → ∀ e : S₂.X₁, φ.τ₂ k = S₂.f e → ∃ b : S₁.X₁, S₁.f b = k) :
    Mono (homologyMap φ) := by
  rw [ModuleCat.mono_iff_injective, ← LinearMap.ker_eq_bot (f := (homologyMap φ).hom),
    LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S₁.homologyπ).1 inferInstance a
  have h0 : S₂.homologyπ (cyclesMap φ c) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← homologyπ_naturality, ConcreteCategory.comp_apply]
    exact ha
  obtain ⟨e, he⟩ := moduleCat_exists_toCycles_eq S₂ _ h0
  obtain ⟨b, hb⟩ := h (S₁.iCycles c) (moduleCat_g_iCycles S₁ c) e (by
    rw [← ConcreteCategory.comp_apply, ← cyclesMap_i, ConcreteCategory.comp_apply, ← he,
      ← ConcreteCategory.comp_apply, toCycles_i])
  have : S₁.toCycles b = c := by
    apply (ModuleCat.mono_iff_injective S₁.iCycles).1 inferInstance
    rw [← ConcreteCategory.comp_apply, toCycles_i, hb]
  rw [← this, ← ConcreteCategory.comp_apply, toCycles_comp_homologyπ]; rfl

end MMP.ModuleCatShortComplex

namespace MMP.ModuleCatComplex

open _root_.HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

/-- In degree `i`, the kernel of the projection onto `coker f` is the image of `f`. -/
lemma exists_f_eq_of_cokernel_π_eq_zero {A B : HomologicalComplex (ModuleCat.{u} R) c}
    (f : A ⟶ B) [Mono f] (i : ι) (b : B.X i) (hb : (cokernel.π f).f i b = 0) :
    ∃ a : A.X i, f.f i a = b := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  exact (ShortComplex.moduleCat_exact_iff _).1
    (hS.map_of_exact (HomologicalComplex.eval _ _ i)).exact b hb

/-- **An elementwise criterion for the comparison map from a cokernel to be a quasi-isomorphism.**
For a monomorphism `f : A ⟶ B` and `g : B ⟶ D` with `f ≫ g = 0`, the induced map
`coker f ⟶ D` is a quasi-isomorphism if (S) every cycle of `D` is, up to a boundary, the image
of a chain of `B` whose differential comes from `A`, and (I) such a chain of `B` whose image in
`D` is a boundary is a boundary up to a chain from `A`. -/
lemma quasiIso_cokernelDesc_of_forall {A B D : HomologicalComplex (ModuleCat.{u} R) c}
    (f : A ⟶ B) [Mono f] (g : B ⟶ D) (w : f ≫ g = 0)
    (hS : ∀ i j k, c.next i = j → c.prev i = k → ∀ z : D.X i, D.d i j z = 0 →
      ∃ b : B.X i, (∃ a : A.X j, B.d i j b = f.f j a) ∧ ∃ e : D.X k, g.f i b - z = D.d k i e)
    (hI : ∀ i j k, c.next i = j → c.prev i = k → ∀ b : B.X i,
      (∃ a : A.X j, B.d i j b = f.f j a) → ∀ e : D.X k, g.f i b = D.d k i e →
      ∃ b' : B.X k, ∃ a' : A.X i, b = B.d k i b' + f.f i a') :
    QuasiIso (cokernel.desc f g w) := by
  set φ := cokernel.desc f g w
  have hφ : ∀ i (b : B.X i), φ.f i ((cokernel.π f).f i b) = g.f i b := fun i b ↦ by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, cokernel.π_desc]
  have hπd : ∀ i j (b : B.X i), (cokernel.π f).f j (B.d i j b) =
      (cokernel f).d i j ((cokernel.π f).f i b) := fun i j b ↦ by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Hom.comm]
  have hsurj : ∀ i, Function.Surjective ((cokernel.π f).f i) := fun i ↦
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hfπ : ∀ i (a : A.X i), (cokernel.π f).f i (f.f i a) = 0 := fun i a ↦ by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, cokernel.condition]; rfl
  refine ⟨fun i ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ i) := ModuleCatShortComplex.moduleCat_mono_homologyMap _
    (fun k hk e he ↦ by
      obtain ⟨b, rfl⟩ := hsurj i k
      have hdb : ∃ a : A.X (c.next i), B.d i (c.next i) b = f.f _ a :=
        (exists_f_eq_of_cokernel_π_eq_zero f _ _ (by rw [hπd]; exact hk)).imp fun _ h ↦ h.symm
      obtain ⟨b', a', hb⟩ := hI i _ _ rfl rfl b hdb e (by rw [← hφ]; exact he)
      refine ⟨(cokernel.π f).f _ b', ?_⟩
      change (cokernel f).d _ i _ = _
      rw [← hπd, hb, map_add, hfπ, add_zero])
  have hepi : Epi (homologyMap φ i) := ModuleCatShortComplex.moduleCat_epi_homologyMap _
    (fun z hz ↦ by
      obtain ⟨b, ⟨a, ha⟩, e, he⟩ := hS i _ _ rfl rfl z hz
      refine ⟨(cokernel.π f).f i b, ?_, e, ?_⟩
      · change (cokernel f).d i _ _ = 0
        rw [← hπd, ha, hfπ]
      · rw [show ((shortComplexFunctor _ c i).map φ).τ₂ ((cokernel.π f).f i b) = g.f i b from
          hφ i b]
        exact he)
  exact isIso_of_mono_of_epi _

section extend

open ComplexShape

variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The differential of the extension of `K` along `embeddingDownNat`, applied to the image of
`x : K.X n`, is the image of `K.d n m x`. -/
lemma extend_d_apply_extendXIso_inv (K : ChainComplex (ModuleCat.{u} R) ℕ) (n m : ℕ)
    (x : K.X n) :
    (K.extend embeddingDownNat).d (embeddingDownNat.f n) (embeddingDownNat.f m)
      ((K.extendXIso embeddingDownNat rfl).inv x) =
      (K.extendXIso embeddingDownNat rfl).inv (K.d n m x) := by
  rw [extend_d_eq K embeddingDownNat rfl rfl, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]

/-- The extension of `φ` along `embeddingDownNat`, applied to the image of `x : K.X n`, is the
image of `φ.f n x`. -/
lemma extendMap_f_apply_extendXIso_inv (φ : K ⟶ L) (n : ℕ) (x : K.X n) :
    (extendMap φ embeddingDownNat).f (embeddingDownNat.f n)
      ((K.extendXIso embeddingDownNat rfl).inv x) =
      (L.extendXIso embeddingDownNat rfl).inv (φ.f n x) := by
  rw [extendMap_f φ embeddingDownNat rfl, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]

/-- `(K.extendXIso embeddingDownNat rfl).inv` is a left inverse of its `hom`, elementwise. -/
lemma extendXIso_inv_hom_apply (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (y : (K.extend embeddingDownNat).X (embeddingDownNat.f n)) :
    (K.extendXIso embeddingDownNat rfl).inv ((K.extendXIso embeddingDownNat rfl).hom y) = y := by
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]; rfl

/-- The inverse of `K.extendXIso embeddingDownNat rfl` is injective. -/
lemma extendXIso_inv_injective (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Injective (K.extendXIso embeddingDownNat (rfl : embeddingDownNat.f n = _)).inv :=
  fun x y h ↦ by
    have := congrArg (K.extendXIso embeddingDownNat rfl).hom h
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Iso.inv_hom_id] at this

/-- In a degree `i` outside the image of `embeddingDownNat`, the module of the extension of `K`
is a subsingleton. -/
lemma subsingleton_extend_X_of_not (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℤ)
    (hi : ∀ n, embeddingDownNat.f n ≠ i) : Subsingleton ((K.extend embeddingDownNat).X i) :=
  (ModuleCat.isZero_iff_subsingleton).1 (isZero_extend_X K embeddingDownNat i hi)

/-- The degree `1` is not in the image of `embeddingDownNat`. -/
lemma embeddingDownNat_f_ne_one (n : ℕ) : embeddingDownNat.f n ≠ 1 := by
  rw [embeddingDownNat_f]; omega

/-- **The cokernel criterion for complexes extended from `ℕ` to `ℤ`.** For chain complexes
`A, B, D` indexed by `ℕ`, maps `f : A ⟶ B` and `g : B ⟶ D`, the comparison map from the cokernel
of the extended `f` to the extended `D` is a quasi-isomorphism once the elementwise conditions
(S) and (I) hold in every degree `n` of the `ℕ`-indexed complexes. -/
theorem quasiIso_cokernelDesc_extendMap_of_forall {A B D : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : A ⟶ B) (g : B ⟶ D) [Mono (extendMap f embeddingDownNat)]
    (w : extendMap f embeddingDownNat ≫ extendMap g embeddingDownNat = 0)
    (hS : ∀ n (z : D.X n), (∀ m, m + 1 = n → D.d n m z = 0) →
      ∃ b : B.X n, (∀ m, m + 1 = n → ∃ a : A.X m, B.d n m b = f.f m a) ∧
        ∃ e : D.X (n + 1), g.f n b - z = D.d (n + 1) n e)
    (hI : ∀ n (b : B.X n), (∀ m, m + 1 = n → ∃ a : A.X m, B.d n m b = f.f m a) →
      ∀ e : D.X (n + 1), g.f n b = D.d (n + 1) n e →
      ∃ b' : B.X (n + 1), ∃ a' : A.X n, b = B.d (n + 1) n b' + f.f n a') :
    QuasiIso (cokernel.desc _ _ w) := by
  refine quasiIso_cokernelDesc_of_forall _ _ w ?_ ?_
  · intro i j k hj hk z hz
    rw [CochainComplex.next] at hj
    rw [CochainComplex.prev] at hk
    by_cases hi : ∃ n, embeddingDownNat.f n = i
    · obtain ⟨n, rfl⟩ := hi
      obtain rfl : k = embeddingDownNat.f (n + 1) := by
        rw [← hk, embeddingDownNat_f, embeddingDownNat_f]; push_cast; ring
      obtain ⟨z₀, rfl⟩ : ∃ z₀, (D.extendXIso embeddingDownNat rfl).inv z₀ = z :=
        ⟨_, extendXIso_inv_hom_apply D n z⟩
      rcases n with _ | m
      · obtain rfl : j = 1 := by rw [← hj, embeddingDownNat_f]; simp
        obtain ⟨b₀, -, e₀, he₀⟩ := hS 0 z₀ (fun m hm ↦ absurd hm (by omega))
        refine ⟨(B.extendXIso embeddingDownNat rfl).inv b₀, ⟨0, ?_⟩,
          (D.extendXIso embeddingDownNat rfl).inv e₀, ?_⟩
        · have := subsingleton_extend_X_of_not B 1 embeddingDownNat_f_ne_one
          exact Subsingleton.elim _ _
        · rw [extendMap_f_apply_extendXIso_inv, ← map_sub, he₀, extend_d_apply_extendXIso_inv]
      · obtain rfl : j = embeddingDownNat.f m := by
          rw [← hj, embeddingDownNat_f, embeddingDownNat_f]; push_cast; ring
        rw [extend_d_apply_extendXIso_inv] at hz
        have hz₀ : D.d (m + 1) m z₀ = 0 :=
          extendXIso_inv_injective D m (by rw [hz, map_zero])
        obtain ⟨b₀, hb₀, e₀, he₀⟩ := hS (m + 1) z₀ (fun m' hm' ↦ by
          obtain rfl : m' = m := by omega
          exact hz₀)
        obtain ⟨a₀, ha₀⟩ := hb₀ m rfl
        refine ⟨(B.extendXIso embeddingDownNat rfl).inv b₀,
          ⟨(A.extendXIso embeddingDownNat rfl).inv a₀, ?_⟩,
          (D.extendXIso embeddingDownNat rfl).inv e₀, ?_⟩
        · rw [extend_d_apply_extendXIso_inv, extendMap_f_apply_extendXIso_inv, ha₀]
        · rw [extendMap_f_apply_extendXIso_inv, ← map_sub, he₀, extend_d_apply_extendXIso_inv]
    · push Not at hi
      have := subsingleton_extend_X_of_not D i hi
      have := subsingleton_extend_X_of_not B i hi
      exact ⟨0, ⟨0, by simp⟩, 0, Subsingleton.elim _ _⟩
  · intro i j k hj hk b hb e he
    rw [CochainComplex.next] at hj
    rw [CochainComplex.prev] at hk
    by_cases hi : ∃ n, embeddingDownNat.f n = i
    · obtain ⟨n, rfl⟩ := hi
      obtain rfl : k = embeddingDownNat.f (n + 1) := by
        rw [← hk, embeddingDownNat_f, embeddingDownNat_f]; push_cast; ring
      obtain ⟨b₀, rfl⟩ : ∃ b₀, (B.extendXIso embeddingDownNat rfl).inv b₀ = b :=
        ⟨_, extendXIso_inv_hom_apply B n b⟩
      obtain ⟨e₀, rfl⟩ : ∃ e₀, (D.extendXIso embeddingDownNat rfl).inv e₀ = e :=
        ⟨_, extendXIso_inv_hom_apply D (n + 1) e⟩
      rw [extendMap_f_apply_extendXIso_inv, extend_d_apply_extendXIso_inv] at he
      have he₀ := extendXIso_inv_injective D n he
      have hb₀ : ∀ m, m + 1 = n → ∃ a : A.X m, B.d n m b₀ = f.f m a := by
        rintro m rfl
        obtain rfl : j = embeddingDownNat.f m := by
          rw [← hj, embeddingDownNat_f, embeddingDownNat_f]; push_cast; ring
        obtain ⟨a, ha⟩ := hb
        obtain ⟨a₀, rfl⟩ : ∃ a₀, (A.extendXIso embeddingDownNat rfl).inv a₀ = a :=
          ⟨_, extendXIso_inv_hom_apply A m a⟩
        rw [extend_d_apply_extendXIso_inv, extendMap_f_apply_extendXIso_inv] at ha
        exact ⟨a₀, extendXIso_inv_injective B m ha⟩
      obtain ⟨b', a', hb'⟩ := hI n b₀ hb₀ e₀ he₀
      refine ⟨(B.extendXIso embeddingDownNat rfl).inv b',
        (A.extendXIso embeddingDownNat rfl).inv a', ?_⟩
      rw [extend_d_apply_extendXIso_inv, extendMap_f_apply_extendXIso_inv, ← map_add, ← hb']
    · push Not at hi
      have := subsingleton_extend_X_of_not B i hi
      exact ⟨0, 0, Subsingleton.elim _ _⟩

end extend

end MMP.ModuleCatComplex
