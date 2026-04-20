{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core

module Categories.Category.Extensive.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Categories.Category.Extensive using (Extensive)
open import Categories.Diagram.Pullback using (Pullback; IsPullback)
open import Categories.Object.Coproduct using (IsCoproduct)
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open Category 𝒞
open M 𝒞
open MR 𝒞
open HomReasoning
open Equiv

module _ (extensive : Extensive 𝒞) where
  open Extensive extensive
  open CC using (_+_; i₁; i₂; ¡; +₁∘i₁; +₁∘i₂; ¡-unique₂; _+₁_; [_,_]; inject₁; inject₂; ∘-distribˡ-[])

  -- The naturality square for i₁ is a pullback in any extensive category
  i₁-naturalitySquare-isPullback : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D)
    → IsPullback 𝒞 f i₁ i₁ (f +₁ g)

  i₁-naturalitySquare-isPullback {A} {B} {C} {D} f g = record
                                                        { commute = sym +₁∘i₁
                                                        ; universal = universal
                                                        ; p₁∘universal≈h₁ = p₁∘universal≈h₁
                                                        ; p₂∘universal≈h₂ = p₂∘universal≈h₂
                                                        ; unique-diagram = λ _ eq₂ → pullback₁-is-mono _ _ eq₂
                                                        }
    where
      open Pullback using (p₁; p₂; commute)
      universal : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C}
        → i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂ → Q ⇒ A
      universal {_} {h₁} {h₂} eq = CP.[ p₂ pb₁ , ¡ ∘ u ]
        where
          pb₁ = pullback₁ h₂
          pb₂ = pullback₂ h₂
          module CP = IsCoproduct (pullback-of-cp-is-cp h₂)
          disj-eq : i₁ ∘ (h₁ ∘ p₁ pb₂) ≈ i₂ ∘ (g ∘ p₂ pb₂)
          disj-eq = begin
            i₁ ∘ h₁ ∘ p₁ pb₂             ≈⟨ extendʳ eq ⟩
            (f +₁ g) ∘ h₂ ∘ p₁ pb₂       ≈⟨ refl⟩∘⟨ commute pb₂ ⟩
            (f +₁ g) ∘ i₂ ∘ p₂ pb₂       ≈⟨ extendʳ +₁∘i₂ ⟩
            i₂ ∘ g ∘ p₂ pb₂              ∎
          u = IsPullback.universal disjoint disj-eq

      p₁∘universal≈h₁ : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C}
        {eq : i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂}
        → f ∘ universal eq ≈ h₁
      p₁∘universal≈h₁ {_} {h₁} {h₂} {eq} =
        let pb₁ = pullback₁ h₂
            pb₂ = pullback₂ h₂
            cp  = pullback-of-cp-is-cp h₂
            disj-eq : i₁ ∘ (h₁ ∘ p₁ pb₂) ≈ i₂ ∘ (g ∘ p₂ pb₂)
            disj-eq = begin
              i₁ ∘ h₁ ∘ p₁ pb₂       ≈⟨ extendʳ eq ⟩ 
              (f +₁ g) ∘ h₂ ∘ p₁ pb₂ ≈⟨ refl⟩∘⟨ commute pb₂ ⟩
              (f +₁ g) ∘ i₂ ∘ p₂ pb₂ ≈⟨ extendʳ inject₂ ⟩ 
              i₂ ∘ g ∘ p₂ pb₂        ∎
            u = IsPullback.universal disjoint disj-eq
            -- h₁ ∘ p₁ pb₁ = f ∘ p₂ pb₁, by mono of i₁
            h₁-pb₁ : h₁ ∘ p₁ pb₁ ≈ f ∘ p₂ pb₁
            h₁-pb₁ = pullback₁-is-mono _ _ (begin
              i₁ ∘ h₁ ∘ p₁ pb₁       ≈⟨ extendʳ eq ⟩ 
              (f +₁ g) ∘ h₂ ∘ p₁ pb₁ ≈⟨ refl⟩∘⟨ commute pb₁ ⟩
              (f +₁ g) ∘ i₁ ∘ p₂ pb₁ ≈⟨ extendʳ +₁∘i₁ ⟩ 
              i₁ ∘ f ∘ p₂ pb₁        ∎)
            -- h₁ ∘ p₁ pb₂ = ¡ ∘ u, from disjoint.p₁∘universal
            h₁-pb₂ : h₁ ∘ p₁ pb₂ ≈ ¡ ∘ u
            h₁-pb₂ = sym (IsPullback.p₁∘universal≈h₁ disjoint)
        in {!!} {- begin
          f ∘ IsCoproduct.[ cp ] (p₂ pb₁) (¡ ∘ u)
            ≈⟨ ∘-distribˡ-[] ⟩
          [ f ∘ p₂ pb₁ , f ∘ ¡ ∘ u ]
            ≈⟨ IsCoproduct.[]-cong₂ cp refl (¡-unique₂ _ _) ⟩
          [ f ∘ p₂ pb₁ , ¡ ∘ u ]
            ≈⟨ IsCoproduct.[]-cong₂ cp (sym h₁-pb₁) (sym h₁-pb₂) ⟩
          [ h₁ ∘ p₁ pb₁ , h₁ ∘ p₁ pb₂ ]
            ≈⟨ sym (IsCoproduct.g-η cp) ⟩
          h₁
          ∎ -}

      p₂∘universal≈h₂ : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C}
        {eq : i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂}
        → i₁ ∘ universal eq ≈ h₂
      p₂∘universal≈h₂ {_} {h₁} {h₂} {eq} =
        let pb₁ = pullback₁ h₂
            pb₂ = pullback₂ h₂
            cp  = pullback-of-cp-is-cp h₂
            disj-eq : i₁ ∘ (h₁ ∘ p₁ pb₂) ≈ i₂ ∘ (g ∘ p₂ pb₂)
            disj-eq = begin
              i₁ ∘ h₁ ∘ p₁ pb₂       ≈⟨ extendʳ eq ⟩ 
              (f +₁ g) ∘ h₂ ∘ p₁ pb₂ ≈⟨ refl⟩∘⟨ commute pb₂ ⟩
              (f +₁ g) ∘ i₂ ∘ p₂ pb₂ ≈⟨ extendʳ +₁∘i₂ ⟩ 
              i₂ ∘ g ∘ p₂ pb₂        ∎
            u = IsPullback.universal disjoint disj-eq
            -- h₂ ∘ p₁ pb₁ = i₁ ∘ p₂ pb₁, by pullback commute
            h₂-pb₁ : h₂ ∘ p₁ pb₁ ≈ i₁ ∘ p₂ pb₁
            h₂-pb₁ = commute pb₁
            -- h₂ ∘ p₁ pb₂ = i₂ ∘ p₂ pb₂ = ¡ ∘ u? We use ¡-unique₂
            h₂-pb₂ : h₂ ∘ p₁ pb₂ ≈ ¡ ∘ u
            h₂-pb₂ = begin
              h₂ ∘ p₁ pb₂  ≈⟨ commute pb₂ ⟩
              i₂ ∘ p₂ pb₂  ≈⟨ {!!} ⟩ -- ¡-unique₂ _ _ ⟩
              ¡ ∘ u         ∎
        in {!!} {- begin
          i₁ ∘ IsCoproduct.[ cp ] (p₂ pb₁) (¡ ∘ u)
            ≈⟨ ∘-distribˡ-[] ⟩
          [ i₁ ∘ p₂ pb₁ , i₁ ∘ ¡ ∘ u ]
            ≈⟨ IsCoproduct.[]-cong₂ cp refl (¡-unique₂ _ _) ⟩
          [ i₁ ∘ p₂ pb₁ , ¡ ∘ u ]
            ≈⟨ IsCoproduct.[]-cong₂ cp (sym h₂-pb₁) (sym h₂-pb₂) ⟩
          [ h₂ ∘ p₁ pb₁ , h₂ ∘ p₁ pb₂ ]
            ≈⟨ sym (IsCoproduct.g-η cp) ⟩
          h₂
          ∎ 
          -}
