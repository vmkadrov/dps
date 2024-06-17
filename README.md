# Алгоритм нахождения коэффициентов для разностных схем

Программа написана для использования в среде Sage 9.2. Полные примеры использования можно найти в *examples*

1. [Рассчет коэффициентов](#рассчет-коэффициентов)
2. [Численные эксперименты](#численные-эксперименты)

## Рассчет коэффициентов

Задание схемы:
```python
sage: load("dps.sage")
sage: s = Scheme([x,t],[f,L], param, rk4(), order = 4)
```

## Численные эксперименты

Функция *dps()* (рассчета по схемам) основана на пакете [fdm](https://github.com/malykhmd/fdm). Импорт в интерфейсе IPython Notebook:
```python
!git clone https://github.com/malykhmd/fdm
%cd fdm
load('fdm.sage')
%cd ..
!rm -rf fdm/ 
```