# Huffman

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[travis-shield]: https://travis-ci.com/coq-community/huffman.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/huffman/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://coq-community.github.io/huffman/toc.html


This projects contains a Coq proof of the correctness of the Huffman coding algorithm,
as described in David A. Huffman's paper A Method for the Construction of Minimum-Redundancy
Codes, Proc. IRE, pp. 1098-1101, September 1952.

## Meta

- Author(s):
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.7 or later
- Additional Coq dependencies: none
- Coq namespace: `Huffman`
- Related publication(s):
  - [Formalising Huffman's algorithm](https://hal.archives-ouvertes.fr/hal-02149909) 
  - [A Method for the Construction of Minimum-Redundancy Codes](http://compression.ru/download/articles/huff/huffman_1952_minimum-redundancy-codes.pdf) doi:[10.1109/JRPROC.1952.273898](https://doi.org/10.1109/JRPROC.1952.273898)

## Building and installation instructions

The easiest way to install the latest released version of Huffman
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-huffman
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/huffman
cd huffman
make   # or make -j <number-of-cores-on-your-machine>
make install
```


## Documentation

For more information about the project, see the [technical report][techreport]
describing the formalization. See also the [coqdoc presentation][coqdoc] of the
Coq source files.

### Running extracted code

To run the extracted algorithm, build the project and then run
```
make run_huffman.ml
```

Next, open an OCaml toplevel (e.g., `ocaml`) and do
```ocaml
#use "run_huffman.ml";;
```

To get the code that gives the frequency string:  
```ocaml
let code = huffman "abbcccddddeeeee";;
```

To code a string:
```ocaml
let c = encode code "abcde";;
```

To decode a string:
```ocaml
decode code c;;
```

[techreport]: https://hal.archives-ouvertes.fr/hal-02149909
[coqdoc]: https://coq-community.github.io/huffman/toc.html
