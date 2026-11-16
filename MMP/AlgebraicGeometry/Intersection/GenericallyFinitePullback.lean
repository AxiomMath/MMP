module
public import MMP.AlgebraicGeometry.Intersection.KleimanTransversality

/-!
# Top intersection numbers under a generically finite morphism

Let `g : X' ⟶ X` be a proper dominant morphism of integral schemes that are proper over a field
`k`, both of dimension `n`, and let `L₁, …, L_n` be invertible sheaves on `X`. Then the top
intersection number of the pull-backs is the function-field degree times that of the `Lᵢ`:
`(g^*L₁ ⋯ g^*L_n) = [k(X') : k(X)] · (L₁ ⋯ L_n)`. The morphism need not be finite.

## Main results

* `MMP.Mori.sheafIntersectionNumber_pullback_eq_finrank_mul`

## Implementation notes

The Cartier divisors `Lⱼ` of the source enter through their invertible sheaves `𝒪_X(Lⱼ)`, and
`g^*Lⱼ` through the pull-back sheaf `g^*𝒪_X(Lⱼ) ≅ 𝒪_{X'}(g^*Lⱼ)`. The statement is made for all
invertible sheaves. Projective varieties are replaced by integral schemes proper over an
arbitrary field. `X'` is a `k`-scheme through `g ≫ f`, and properness of `g` is the same as
properness of `X'` over `k`. Surjectivity is weakened to dominance, since a proper dominant
morphism is surjective. The degree `[k(X') : k(X)]` is `Module.finrank` for the extension
`MMP.Mori.functionFieldMapAlgebra g`, which is finite because the dimensions are equal.

Both intersection numbers are the coefficients of `n₁ ⋯ n_n` in the Snapper polynomials of the
two families, and the degree-`n` homogeneous components of those polynomials differ by
`[k(X') : k(X)]` (`homogeneousComponent_eulerPolynomial_pullback_eq_finrank_smul`).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.35
-/

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

universe u

namespace MMP.Mori

/-- Isomorphic families of invertible modules give isomorphic folds of twists. -/
private noncomputable def twistListFamilyIso {X : Scheme.{u}} {r : ℕ} (L M : Fin r → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, L j ≅ M j) (n : Fin r → ℤ) (l : List (Fin r)) :
    ∀ {F G : X.Modules}, (F ≅ G) → (twistList L n l F ≅ twistList M n l G) := by
  induction l with
  | nil => exact fun ε => ε
  | cons j t ih =>
    exact fun ε => ih (tensorProductIso X.presheaf X.ringCatSheaf.2 ε
      (Twist.tensorPowerIsoOfIso (L j) (M j) (e j) (n j)))

/-- The Euler characteristic over a structure morphism `ψ` equal to `φ` is that over `φ`. -/
private theorem eulerCharacteristic_congr_hom (k : Type u) [Field k] {Y : Scheme.{u}}
    {φ ψ : Y ⟶ Spec (.of k)} [IsProper φ] [IsProper ψ] (h : ψ = φ) (F : Y.Modules)
    [F.IsCoherent] : eulerCharacteristic k ψ F = eulerCharacteristic k φ F := by
  subst h; rfl

/-- The intersection number of `M₁, …, M_d` on `Y` itself is the coefficient of `n₁ ⋯ n_d` in any
polynomial of total degree at most `d` interpolating `n ↦ χ(Y, M₁^{n₁} ⊗ ⋯ ⊗ M_d^{n_d})`. -/
private theorem sheafIntersectionNumber_id_eq_coeff (k : Type u) [Field k] {Y : Scheme.{u}}
    (φ : Y ⟶ Spec (.of k)) [IsProper φ] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (M : Fin d → Y.Modules) [∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (M j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (@eulerCharacteristic k _ Y φ _ (twistedSheaf (SheafOfModules.unit Y.ringCatSheaf) M n)
        (@twistedSheaf_isCoherent Y d _ M _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k φ) n) : ℚ))
    (hdeg : P.totalDegree ≤ d) :
    (sheafIntersectionNumber k φ (𝟙 Y) d hd M : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_eq_coeff k φ (𝟙 Y) d hd M P (fun n => ?_) hdeg
  rw [hP n]
  congr 1
  rw [eulerCharacteristic_congr_hom k (Category.id_comp φ)]
  have e : twistedSheaf (SheafOfModules.unit Y.ringCatSheaf) M n ≅
      twistedSheaf (SheafOfModules.unit Y.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback (𝟙 Y)).obj (M j)) n :=
    twistListFamilyIso M _ (fun j => ((Scheme.Modules.pullbackId Y).app (M j)).symm) n
      (List.finRange d) (Iso.refl _)
  exact @eulerCharacteristic_eq_of_iso k _ Y φ _ _ _
    (@twistedSheaf_isCoherent Y d _ M _
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k φ) n)
    (isCoherent_twistedSheafUnitPullback k φ (𝟙 Y) M n) e

/-- The Snapper polynomial of a family on a proper `k`-scheme of dimension at most `d`, with its
values and its degree bound. -/
private theorem exists_eulerPolynomial (k : Type u) [Field k] {Y : Scheme.{u}}
    (φ : Y ⟶ Spec (.of k)) [IsProper φ] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (M : Fin d → Y.Modules) [∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (M j)] :
    ∃ P : MvPolynomial (Fin d) ℚ, P.totalDegree ≤ d ∧
      ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        (@eulerCharacteristic k _ Y φ _ (twistedSheaf (SheafOfModules.unit Y.ringCatSheaf) M n)
          (@twistedSheaf_isCoherent Y d _ M _
            (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k φ) n) : ℚ) := by
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k φ M
    (SheafOfModules.unit Y.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k φ)
  refine ⟨P, ?_, hP⟩
  rcases hP0 with rfl | h
  · simp
  · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le Y _).trans hd)

/-- **Projection formula for top intersection numbers.** Let `g : X' ⟶ X` be a proper dominant
morphism of integral schemes proper over a field `k` (through `f` and `g ≫ f`), both of
dimension `n`, and let `L₁, …, L_n` be invertible sheaves on `X`. Then
`(g^*L₁ ⋯ g^*L_n · X') = [k(X') : k(X)] · (L₁ ⋯ L_n · X)`. -/
@[mmp "lem_mmp_foundation_km_generically_finite_intersection_projection"]
public theorem sheafIntersectionNumber_pullback_eq_finrank_mul
    (k : Type u) [Field k] {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ Spec (.of k)) [IsProper f] (g : X' ⟶ X) [IsProper g] [IsDominant g]
    (n : ℕ) (hd : topologicalKrullDim X = n) (hd' : topologicalKrullDim X' = n)
    (L : Fin n → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k (g ≫ f) (𝟙 X') n hd'.le
        (fun j => (Scheme.Modules.pullback g).obj (L j)) =
      (letI := functionFieldMapAlgebra g; Module.finrank X.functionField X'.functionField : ℤ) *
        sheafIntersectionNumber k f (𝟙 X) n hd.le L := by
  obtain ⟨P, hPdeg, hP⟩ := exists_eulerPolynomial k (g ≫ f) n hd'.le
    (fun j => (Scheme.Modules.pullback g).obj (L j))
  obtain ⟨Q, hQdeg, hQ⟩ := exists_eulerPolynomial k f n hd.le L
  have hc := congrArg (fun q => AddMonoidAlgebra.coeff q (Finsupp.equivFunOnFinite.symm fun _ => 1))
    (homogeneousComponent_eulerPolynomial_pullback_eq_finrank_smul k f g n hd hd' L P Q hP hQ)
  simp [MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_eq_sum] at hc
  apply Int.cast_injective (α := ℚ)
  rw [sheafIntersectionNumber_id_eq_coeff k (g ≫ f) n hd'.le _ P hP hPdeg, Int.cast_mul,
    sheafIntersectionNumber_id_eq_coeff k f n hd.le L Q hQ hQdeg, hc]
  rfl

end MMP.Mori
