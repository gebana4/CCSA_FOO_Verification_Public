# Mechanized Analysis of Vote Privacy using Computationally Complete Symbolic Attacker

This project aims to provide a mechanized analysis of vote privacy in the FOO electronic voting systems using a computationally complete symbolic attacker(CCSA) model. The focus is on evaluating the vulnerability of such systems to sophisticated adversaries and providing insights into enhancing vote privacy mechanisms.

## Installation

To set up and build this project, follow these steps:

1. Clone this repository:
```
git clone https://github.com/gebana4/CCSA_FOO_Verification_Public
```

2. Make sure you have Coq installed. If you don't have it installed yet, follow the steps on the website: [Coq Installation](https://coq.inria.fr/download)

3. Navigate to the root directory of the project and run the following command to generate the necessary Makefile:
```
coq_makefile -f _CoqProject */*.v -o Makefile
```

4. Once the Makefile is generated, use the `make` command to build the project.



## Authors

- Gergei Bana (Email: banag@missouri.edu)
- Rohit Chadha (Email:  chadhar@missouri.edu)
- Ajay Kumar Eeralla (Email: aeeralla@amd.com)
- Qianli Zhang (Email:  qianli.zhang@mail.missouri.edu)

We sincerely thank all of the authors for their valuable contributions to this project.



## License

This project is licensed under the [MIT License](LICENSE).
