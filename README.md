### lam

#### handle

![handle](/img/handle.jpg)

```
⟦handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk k_f γ.
    ⟦body⟧
      (λv γ'.     ⟦eᵥ⟧  (λx γ'. γ' x) k_f γ')
      (λvₑ vₖ γ'. ⟦e_f⟧ (λx γ'. γ' x) k_f γ')
      (λx. k x γ)
```

#### perform

![perform](/img/perform.jpg)
      
```
⟦perform e⟧ =
  λk k_f γ.
    ⟦e⟧ (λvₑ γ.
      k_f vₑ
          (λf v k' k_f' γ'. ⟦f v⟧ k k_f (λx. k' x γ'))
          γ
    ) k_f γ
```

#### continue

```
⟦continue stack x⟧ =
  λk k_f γ.
    ⟦x⟧ (λv γ.
      ⟦λx. x⟧ (λf γ.
        stack f v k k_f γ
      ) k_f γ
    ) k_f γ
```

#### delegate

```
⟦delegate e stack⟧ =
  λk k_f γ.
    ⟦e⟧ (λvₑ γ.
      k_f vₑ stack γ
    ) k_f γ
```