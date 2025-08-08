# Algoritmo-de-Quine-McCluskey

Implementação do algoritmo de QuineMcCluskey em Rust

Para rodar o programa, é recomenda-se utilizar o gerenciador de pacotes [cargo](https://github.com/rust-lang/cargo). Com ele, basta rodar o comando

`cargo run --release caminho_do_arquivo`

O arquivo de entrada deve estar no formato PLA. O programa foi feito com o objetivo de replicar o comportamento do minimizador lógico Espresso, com os argumentos "-o -eqntott", então o programa não reconhece outros parâmetros descritos na especificação do formato PLA. Apenas são reconhecidos o ".i" para saber o número de variáveis, os mintermos e o .e para finalizar o arquivo.
