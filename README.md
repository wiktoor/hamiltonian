# Hamiltonian group classification

Lean 4 formalization of my bachelor's thesis in mathematics.

## Problem statement

[Hamiltonian group](https://en.wikipedia.org/wiki/Dedekind_group) (a.k.a Dedekind group) `H` is a non-abelian group such that every subgroup of `H` is normal.

The most popular example of a Hamiltonian group is the [quaternion group](https://en.wikipedia.org/wiki/Quaternion_group) `Q8`.

Dedekind and Baer showed that a group `H` is Hamiltonian if and only if it's of form `Q8 x U x V`, where
- `U` is an abelian (torsion) group with all elements of odd orders
- `V` is an abelian group with all elements of order less of equal `2` ([elementary abelian 2-group](https://en.wikipedia.org/wiki/Elementary_abelian_group)).

Equivalently, `H = Q8 x A`, where `A` is an abelian group that does not contain an element of order `4`.

## Bachelor's thesis

In my bachelor's thesis I presented my proof of Dedekind and Baer result, based on [The theory of groups by Marshall Hall](https://ia601508.us.archive.org/29/items/in.ernet.dli.2015.84699/2015.84699.The-Theory-Of-Groups-Vol-I_text.pdf).

You can see my proof (in Polish) in `/files/licencjat.pdf`.

## Use of AI

At first, I tried to formalize this without the use of AI. It turned out to be too difficult and time-consuming, so I decided to write the definitions and theorems I used in my proof and asked `Claude Opus 5.5` to fill in the details.

## Usage

If you want to verify the proof yourself, use:
```sh
lake build
```
