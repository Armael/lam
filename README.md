### lam

#### handle

![handle](/img/handle.jpg)

```
⟦handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk k_f.
    k (⟦body⟧
         (λv.     ⟦eᵥ⟧  (λv. v) k_f)
         (λvₑ vₖ. ⟦e_f⟧ (λv. v) k_f))
```

---

With meta-continuations:
```
⟦handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk k_f γ.
    ⟦body⟧
      (λv γ'.     ⟦eᵥ⟧  (λx γ'. γ' x) k_f γ')
      (λvₑ vₖ γ'. ⟦e_f⟧ (λx γ'. γ' x) k_f γ')
      (λx. k x γ)
```

Sugar-free version:
```
⟦handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk k_f γ.
    ⟦body⟧
      (λv.     ⟦eᵥ⟧  (λx γ'. γ' x) k_f)
      (λvₑ vₖ. ⟦e_f⟧ (λx γ'. γ' x) k_f)
      (λx. k x γ)
```

#### perform

![perform](/img/perform.jpg)
      
```
⟦perform e⟧ =
  λk k_f.
    ⟦e⟧ (λvₑ.
      k_f vₑ (λf v. f v k k_f)
    ) k_f
```

---

With meta-continuations:
```
⟦perform e⟧ =
  λk k_f γ.
    ⟦e⟧ (λvₑ γ.
      k_f vₑ
          (λf v k' k_f' γ'. f v k k_f (λx. k' x γ'))
          γ
    ) k_f γ
```

Sugar-free version:
```
⟦perform e⟧ =
  λk k_f.
    ⟦e⟧ (λvₑ.
      k_f vₑ (λf v k' k_f' γ'. f v k k_f (λx. k' x γ'))
    ) k_f
```

#### continue

```
⟦continue stack e⟧ =
  λk k_f.
    ⟦x⟧ (λv.
      ⟦stack⟧ (λstack.
        k (stack (λx k k_f. k x) v)
      ) k_f
    ) k_f
```

---

With meta-continuations:
```
⟦continue stack x⟧ =
  λk k_f γ.
    ⟦x⟧ (λv γ.
      ⟦stack⟧ (λstack γ.
        ⟦λx. x⟧ (λf γ.
          stack f v k k_f γ
        ) k_f γ
      ) k_f γ
    ) k_f γ
```

Sugar-free version:
```
⟦continue stack x⟧ =
  λk k_f.
    ⟦x⟧ (λv.
      ⟦stack⟧ (λstack γ.
        stack (λx k k_f. k x) v k k_f
      ) k_f
    ) k_f
```

#### delegate

```
⟦delegate e stack⟧ =
  λk k_f.
    ⟦stack⟧ (λstack.
      ⟦e⟧ (λvₑ.
        k_f vₑ stack
      ) k_f
    ) k_f
```

---

With meta-continuations:
```
⟦delegate e stack⟧ =
  λk k_f γ.
    ⟦stack⟧ (λstack γ.
      ⟦e⟧ (λvₑ γ.
        k_f vₑ stack γ
      ) k_f γ
    ) k_f γ
```
