use std::collections::BTreeSet;
use std::env;
use std::fs::File;
use std::io::{BufReader, Read};

mod min_term {
    use itertools::{Either, Itertools};
    use std::collections::{BTreeMap, BTreeSet};
    use std::iter::zip;
    use std::ops::Not;

    // O mintermo é aqui descrito como um vetor de bytes. Lembrando que cada byte corresponde a uma
    // variável. Os implicantes também são representados por essa estrutura.
    // Em vez de u8, poderia ser utilizado um enum, já que os valores possível são apenas 1, 0 e
    // '-'. Foi escolhida a primeira abordagem por simplicidade.
    #[derive(Debug, Clone)]
    pub struct MinTerm {
        bits: Vec<u8>,
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum CoverageMark {
        EssentialPrimeImplicant, // Marca que o mintermo é coberto por um implicante primo essencial
        NotCovered,              // Marca que o mintermo não é coberto por determinado implicante
        NonEssentialPrimeImplicant, // Marca que o mintermo é coberto por um implicante primo não essencial
        EssentialCover, // Marca que o mintermo é coberto por implicante primo não essencial e
                        // também por um implicante primo essencial. Essa variante será utilizada
                        // para simplificar no algoritmo de Petrick, visto que se um implicante
                        // primo cobre apenas mintermos já cobertos por implicantes primos, que
                        // obrigatoriamente já aparecem na solução final, não tem porque
                        // adicioná-lo.
    }

    impl MinTerm {
        pub fn count_dashes(&self) -> usize {
            self.bits.iter().filter(|&&x| x == b'-').count()
        }

        fn to_expression(&self) {
            let mut iter = self.bits.iter().enumerate().filter(|(_, x)| **x != b'-');
            let last = iter.next_back();

            print!("(");
            iter.for_each(|(idx, &x)| match x {
                b'1' => print!("v{idx}&"),
                b'0' => print!("!v{idx}&"),
                _ => unreachable!(),
            });

            match last {
                Some((idx, b'1')) => print!("v{idx}"),
                Some((idx, b'0')) => print!("!v{idx}"),
                _ => unreachable!(),
            }
            print!(")");
        }
    }

    impl From<&str> for MinTerm {
        fn from(value: &str) -> Self {
            MinTerm {
                bits: value.as_bytes().into(),
            }
        }
    }

    impl From<Vec<u8>> for MinTerm {
        fn from(value: Vec<u8>) -> Self {
            MinTerm { bits: value }
        }
    }

    impl<'a> IntoIterator for &'a MinTerm {
        type Item = &'a u8;

        type IntoIter = std::slice::Iter<'a, u8>;

        fn into_iter(self) -> Self::IntoIter {
            self.bits.iter()
        }
    }

    impl Ord for MinTerm {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            use std::cmp::Ordering::*;
            for (a, b) in zip(&self.bits, &other.bits) {
                if a != b {
                    return b.cmp(a);
                }
            }

            Equal
        }
    }

    impl PartialOrd for MinTerm {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    impl PartialEq for MinTerm {
        fn eq(&self, other: &Self) -> bool {
            zip(self, other).all_equal()
        }
    }

    impl Eq for MinTerm {}

    // Combina dois mintermos (ou implicantes)
    fn merge_minterms(first: &MinTerm, second: &MinTerm) -> MinTerm {
        zip(first, second)
            .map(|(x, y)| if x != y { b'-' } else { *x })
            .collect::<Vec<u8>>()
            .into()
    }

    // Verifica se os hífens dos mintermos estão alinhados. Essa condição é necessária para a
    // combinação dos mintermos.
    fn check_dashes_align(first: &MinTerm, second: &MinTerm) -> bool {
        zip(first, second)
            .any(|(&x, &y)| (x == b'-') ^ (y == b'-'))
            .not()
    }

    // Verifica se os mintermos diferem em apenas 1 bit
    fn check_min_term_difference(first: &MinTerm, second: &MinTerm) -> bool {
        zip(first, second).filter(|(x, y)| x != y).count() == 1
    }

    fn check_match_prime_implicant_and_minterm(
        prime_implicant: &MinTerm,
        minterms: &MinTerm,
    ) -> bool {
        zip(prime_implicant, minterms).all(|(&x, &y)| x == b'-' || y == b'-' || x == y)
    }

    // Verifica a marcação mais apropriada
    fn mark_coverage(first: &mut [CoverageMark], second: &mut [CoverageMark]) {
        use CoverageMark::*;
        for idx in 0..first.len() {
            match (first[idx], second[idx]) {
                // Se dois implicantes primos essencias cobrem o mesmo mintermo, na verdade nenhum
                // deles é essencial
                (EssentialPrimeImplicant, EssentialPrimeImplicant) => {
                    first[idx] = NonEssentialPrimeImplicant;
                    second[idx] = NonEssentialPrimeImplicant;
                }
                // Se um implicante primos essencial cobre o mesmo mintermo que um não essencial,
                // ele também é não essencial
                (NonEssentialPrimeImplicant, EssentialPrimeImplicant) => {
                    second[idx] = NonEssentialPrimeImplicant;
                }
                (EssentialPrimeImplicant, NonEssentialPrimeImplicant) => {
                    first[idx] = NonEssentialPrimeImplicant;
                }
                // Qualquer outra combinação não sofre alteração
                _ => (),
            }
        }
    }

    // Verifica se o implicante primo não essencial cobre mintermos que já são cobertos por um
    // implicante primo esssencial
    fn mark_redundancy(essential: &[CoverageMark], non_essential: &mut [CoverageMark]) {
        use CoverageMark::*;
        for idx in 0..essential.len() {
            match (essential[idx], non_essential[idx]) {
                (EssentialPrimeImplicant, NonEssentialPrimeImplicant)
                | (NonEssentialPrimeImplicant, EssentialPrimeImplicant) => {
                    non_essential[idx] = EssentialCover;
                }
                _ => (),
            }
        }
    }

    fn is_essential_prime_implicant(prime_implicant: &[CoverageMark]) -> bool {
        prime_implicant.contains(&CoverageMark::EssentialPrimeImplicant)
    }

    // Encontra os implicantes primos a partir do conjunto de mintermos
    // A estrutura de dados utilizada para manipular os mintermos foi o BTreeSet
    // Utilizando um set, garante-se que cada mintermo aparece apenas uma única vez, mas não
    // varifica caso o mesmo mintermo seja adicionado mais de uma vez com resultados diferentes.
    // O BTreeSet garante a ordenação dos mintermos. Durante o desenvolvimento, percebeu-se que
    // isso é necessário. Mas poderia ser tentada um implementação utilizando HashSet para diminuir
    // o processamento com a ordenação.
    pub fn get_prime_implicants(minterms: &BTreeSet<MinTerm>) -> BTreeSet<MinTerm> {
        // Inicialmente o conjunto de mintermos é clonado. Esse conjunto irá guardar os termos que
        // não foram combinados. Se eles não foram combinados nessa iteração, ou já são implicantes
        // primos ou serão combinados na próxima iteração.
        let mut not_merged: BTreeSet<MinTerm> = BTreeSet::from_iter(minterms.iter().cloned());
        let mut prime_implicants = minterms
            .iter()
            .combinations(2)
            .filter(|v| check_dashes_align(v[0], v[1]) && check_min_term_difference(v[0], v[1]))
            .map(|v| {
                not_merged.remove(v[0]);
                not_merged.remove(v[1]);
                merge_minterms(v[0], v[1])
            })
            .collect::<BTreeSet<MinTerm>>();

        let number_of_merges = prime_implicants.len();

        prime_implicants.extend(not_merged);

        // O algoritmo é recursivo, visto que implicantes ainda podem ser combinados.
        if number_of_merges == 0 {
            prime_implicants
        } else {
            get_prime_implicants(&prime_implicants)
        }
    }

    pub fn create_prime_implicant_chart(
        prime_implicants: &BTreeSet<MinTerm>,
        minterms: &BTreeSet<MinTerm>,
    ) -> BTreeMap<MinTerm, Vec<CoverageMark>> {
        let mut prime_implicant_chart: BTreeMap<MinTerm, Vec<CoverageMark>> = BTreeMap::new();

        for prime_implicant in prime_implicants {
            for minterm in minterms {
                // Todos as marcações são feitas supondo que aquele implicante primo é essencial. A
                // classificação será feita posteriormente.
                let chart_tick =
                    match check_match_prime_implicant_and_minterm(prime_implicant, minterm) {
                        true => CoverageMark::EssentialPrimeImplicant,
                        false => CoverageMark::NotCovered,
                    };
                prime_implicant_chart
                    .entry(prime_implicant.clone())
                    .and_modify(|x| x.push(chart_tick))
                    .or_insert(vec![chart_tick]);
            }
        }

        prime_implicant_chart
    }

    // Classifica os implicantes primos em essenciais e não essenciais.
    pub fn classify_prime_implicants(
        prime_implicant_chart: &mut BTreeMap<MinTerm, Vec<CoverageMark>>,
    ) -> (Vec<MinTerm>, Vec<MinTerm>) {
        let local_prime_implicant_chart = prime_implicant_chart.clone();

        local_prime_implicant_chart
            .keys()
            .combinations(2)
            .for_each(|combination| {
                let (prime_implicant1, mut ticks1) =
                    prime_implicant_chart.remove_entry(combination[0]).unwrap();
                let (prime_implicant2, mut ticks2) =
                    prime_implicant_chart.remove_entry(combination[1]).unwrap();

                mark_coverage(&mut ticks1, &mut ticks2);

                prime_implicant_chart.insert(prime_implicant1, ticks1);
                prime_implicant_chart.insert(prime_implicant2, ticks2);
            });

        prime_implicant_chart
            .iter()
            .partition_map(|(prime_implicant, tick)| {
                if is_essential_prime_implicant(tick) {
                    Either::Left(prime_implicant.clone())
                } else {
                    Either::Right(prime_implicant.clone())
                }
            })
    }

    // Elimina todos os implicantes primos não essenciais redundantes, ou seja, que só cobrem
    // mintermos já cobertos por implicantes primos essenciais
    pub fn eliminate_redundant_non_essential_prime_implicant(
        prime_implicant_chart: &mut BTreeMap<MinTerm, Vec<CoverageMark>>,
        essential_prime_implicants: &[MinTerm],
        non_essential_prime_implicants: Vec<MinTerm>,
    ) -> Vec<MinTerm> {
        essential_prime_implicants
            .iter()
            .cartesian_product(&non_essential_prime_implicants)
            .for_each(|(essential, non_essential)| {
                let (e, e_ticks) = prime_implicant_chart.remove_entry(essential).unwrap();
                let (n, mut ticks) = prime_implicant_chart.remove_entry(non_essential).unwrap();

                mark_redundancy(&e_ticks, &mut ticks);

                prime_implicant_chart.insert(e, e_ticks);
                prime_implicant_chart.insert(n, ticks);
            });

        use CoverageMark::*;
        non_essential_prime_implicants
            .into_iter()
            .filter(|x| {
                prime_implicant_chart
                    .get(x)
                    .unwrap()
                    .iter()
                    .all(|y| matches!(y, EssentialCover | NotCovered))
                    .not()
            })
            .collect()
    }

    pub fn output_expression(minterms: &[MinTerm]) {
        let mut iter = minterms.iter();
        let last = iter.next_back();

        iter.for_each(|x| {
            x.to_expression();
            print!(" | ");
        });

        if let Some(minterm) = last {
            minterm.to_expression();
        }

        println!();
    }
}

mod petrick_method {
    use itertools::Itertools;

    use crate::min_term::MinTerm;
    use std::collections::BTreeSet;

    // Os implicantes primos que estão sendo multiplicados são guardados num BTreeSet. Por exemplo,
    // A.B.C seria armazenado como BTreeSet(A, B, C). Foi escolhido o BTreeSet para garantir
    // unicidade e ordem
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Product<'a>(BTreeSet<&'a MinTerm>);

    // Os implicantes primos que estão sendo somados são guardados num BTreeSet de produtos. Por
    // exemplo A.B.C + D.E seria armazenado como BTreeSet(Produtos(A, B, C), Produtos(D,E)). Foi
    // escolhido o BTreeSet para garantir unicidade e ordem.
    #[derive(Debug)]
    struct Sum<'a>(BTreeSet<Product<'a>>);

    pub fn petrick_method(non_essential_prime_implicants: &[MinTerm]) -> Vec<MinTerm> {
        // Se o número de implicantes primos não essencias é menor que 2, o algoritmo de Petrick
        // não é necessário.
        if non_essential_prime_implicants.len() < 2 {
            return non_essential_prime_implicants.into();
        }

        non_essential_prime_implicants
            .iter()
            .combinations(2)
            .map(|combination| {
                // Sendo K, M e N implicantes primos, o algoritmo de Petrick resulta em (K+M).(K+N).(M+N)
                let minterm1 = Product(BTreeSet::from([combination[0]])); // Exemplo: |K| - |K| - |M|
                let minterm2 = Product(BTreeSet::from([combination[1]])); // Exemplo: |M| - |N| - |N|

                Sum(BTreeSet::from([minterm1, minterm2]))
            })
            .reduce(|acc, x| {
                // O processamento será a multiplicação de um termo de cada vez e da esquerda para
                // a direita, ou seja:
                // (K+M).(K+N).(M+N) => (K+KN+KM+MN).(M+N) => KM+KN+KMN+MN
                // O.B.S: AA = A e A + A = A (BTreeSet não vai aceitar duplicatas)
                Sum(acc
                    .0
                    .iter()
                    .cartesian_product(x.0.iter())
                    .map(|(p1, p2)| {
                        let union = p1.0.union(&p2.0).cloned().collect();
                        Product(union)
                    })
                    .collect())
            })
            .unwrap()
            .0
            .iter()
            .max_by(|x, y| {
                // É selecionado o termo com o mair número de hífens, ou seja, com menor número de
                // variáveis
                let x_dashes_count = x.0.iter().map(|a| a.count_dashes()).sum::<usize>();
                let y_dashes_count = y.0.iter().map(|a| a.count_dashes()).sum::<usize>();

                x_dashes_count.cmp(&y_dashes_count)
            })
            .iter()
            .flat_map(|Product(a)| a)
            .map(|&x| x.clone())
            .collect()
    }
}

fn read_pla_file(file_path: &str) -> std::io::Result<BTreeSet<min_term::MinTerm>> {
    let file = File::open(file_path)?;

    let mut buf_reader = BufReader::new(file);

    let mut buffer = String::new();

    let mut input_variable_number = 0;
    // let mut output_variable_number;

    let mut result = BTreeSet::new();

    buf_reader.read_to_string(&mut buffer)?;
    buffer
        .lines()
        .map(|line| line.split_whitespace())
        .for_each(|mut iter| {
            let first = iter.next().expect("Sintax error 1!");

            match first {
                ".i" => {
                    input_variable_number =
                        iter.next().map(|x| x.parse::<usize>().unwrap()).unwrap()
                }
                // ".o" => output_variable_number = second.parse::<usize>(),
                ".o" | ".e" | ".p" | ".type" => (),
                _ => {
                    if first.len() == input_variable_number {
                        if iter.next().unwrap() == "1" {
                            result.insert(min_term::MinTerm::from(first));
                        }
                    } else {
                        panic!("Sintax error 3!")
                    }
                }
            }
        });

    Ok(result)
}

fn main() {
    if let Some(filepath) = env::args().nth(1) {
        match read_pla_file(&filepath) {
            Ok(minterms) => {
                let prime_implicants = min_term::get_prime_implicants(&minterms);

                let mut prime_implicant_chart =
                    min_term::create_prime_implicant_chart(&prime_implicants, &minterms);

                let (mut essential_prime_implicants, non_essential_prime_implicants) =
                    min_term::classify_prime_implicants(&mut prime_implicant_chart);

                let non_essential_prime_implicants =
                    min_term::eliminate_redundant_non_essential_prime_implicant(
                        &mut prime_implicant_chart,
                        &essential_prime_implicants,
                        non_essential_prime_implicants,
                    );

                let prime_implicant_complement =
                    petrick_method::petrick_method(&non_essential_prime_implicants);

                essential_prime_implicants.extend(prime_implicant_complement);

                min_term::output_expression(&essential_prime_implicants);
            }
            Err(a) => println!("{a}"),
        }
    } else {
        println!("Error: Filepath must be provided")
    }
}
