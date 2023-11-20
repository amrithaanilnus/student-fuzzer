from typing import List, Set, Any, Tuple, Dict, Union
from collections.abc import Sequence
import random
from bug import entrypoint
from bug import get_initial_corpus
from fuzzingbook.Coverage import population_coverage
import string
from fuzzingbook.Coverage import Location
import time
import numpy as np
import matplotlib.pyplot as plt
import pickle   # serializes an object by producing a byte array from all the information in the object
import hashlib
from fuzzingbook import Coverage as cv
from fuzzingbook import MutationFuzzer as mf
from re import I
class Seed:
    """Represent an input with additional attributes"""

    def __init__(self, data: str) -> None:
        """Initialize from seed data"""
        self.data = data
        self.coverage: Set[Location] = set()
        self.distance: Union[int, float] = -1
        self.energy = 0.0
        self.mask= [1 for _ in range(len(data))]

    def __str__(self) -> str:
        """Returns data as string representation of the seed"""
        return self.data

    __repr__ = __str__

class Mutator:

    def __init__(self) -> None:
        """Constructor"""
        self.mutators = [
            self.delete_random_character,
            self.insert_random_character,
            self.flip_random_character
        ]

    def insert_random_character(self, s: Seed) -> str:
         """Returns s with a random character inserted"""

         valid_positions = [pos for pos, mask_bit in enumerate(s.mask) if mask_bit[1] == 1]
         if valid_positions==[]:
          valid_positions.append(len(s.data))
         pos = random.choice(valid_positions)
         random_character = chr(random.randrange(32, 127))
         temp=Seed(s.data[:pos] + random_character + s.data[pos:])
         mask=s.mask[:]
         mask.insert(pos,[1,1,1])
         temp.mask=mask
        return temp


    def delete_random_character(self, s: Seed) -> str:
        """Returns s with a random character deleted"""
        if s.data == "":
            return self.insert_random_character(s)
        valid_positions = [pos for pos, mask_bit in enumerate(s.mask) if mask_bit[2] == 1]
        if valid_positions==[]:
          return self.insert_random_character(s)
        pos = random.choice(valid_positions)
        temp=Seed( s.data[:pos] + s.data[pos + 1:])
        mask1=s.mask[:]
        del mask1[pos]
        temp.mask=mask1
        return temp

    def flip_random_character(self, s: str) -> str:
        #print(s)
        """Returns s with a random bit flipped in a random position"""
        if s.data == "":
            return self.insert_random_character(s)
        valid_positions = [pos for pos, mask_bit in enumerate(s.mask) if mask_bit[0] == 1]
        if valid_positions==[]:
          return self.insert_random_character(s)
        pos = random.choice(valid_positions)
        c = s.data[pos]
        bit = 1 << random.randint(0, 6)
        new_c = chr(ord(c) ^ bit)
        temp=Seed(s.data[:pos] + new_c + s.data[pos + 1:])
        temp.mask=s.mask[:]
        temp.mask[pos]=[1,1,1]
        return temp

    def flip_pos_character(self,pos,s:str)->str:
        if s == "":
            return s
        bit = 1 << random.randint(0, 6)
        c = s[pos]
        new_c = chr(ord(c) ^ bit)
        return s[:pos] + new_c + s[pos + 1:]

    def insert_pos_character(self,pos,s:str)->str:
        random_character = chr(random.randrange(32, 127))
        return s[:pos] + random_character + s[pos:]

    def delete_pos_character(self,pos,s:str) -> str:
        if s == "":
            return s

        return s[:pos] + s[pos + 1:]


    def mutate(self, inp: Seed) -> Any:
        """Return s with a random mutation applied. Can be overloaded in subclasses."""
        mutator = random.choice(self.mutators)
        return mutator(inp)

class PowerSchedule:
    """Define how fuzzing time should be distributed across the population."""

    def __init__(self) -> None:
        """Constructor"""
        self.path_frequency: Dict = {}

    def assignEnergy(self, population: Sequence[Seed]) -> None:
        """Assigns each seed the same energy"""
        for seed in population:
            seed.energy = 1

    def normalizedEnergy(self, population: Sequence[Seed]) -> List[float]:
        """Normalize energy"""
        energy = list(map(lambda seed: seed.energy, population))
        sum_energy = sum(energy)  # Add up all values in energy
        assert sum_energy != 0
        norm_energy = list(map(lambda nrg: nrg / sum_energy, energy))
        return norm_energy

    def choose(self, population: Sequence[Seed]) -> Seed:
        """Choose weighted by normalized energy."""

        #self.assignEnergy(population)

        norm_energy = self.normalizedEnergy(population)
        #print(norm_energy)
        seed: Seed = random.choices(population, weights=norm_energy)[0]
        return seed

from fuzzingbook.MutationFuzzer import FunctionCoverageRunner

from fuzzingbook.Fuzzer import Fuzzer

class AdvancedMutationFuzzer(Fuzzer):
    """Base class for mutation-based fuzzing."""

    def __init__(self, seeds: List[str],
                 mutator: Mutator,
                 schedule: PowerSchedule) -> None:
        """Constructor.
        `seeds` - a list of (input) strings to mutate.
        `mutator` - the mutator to apply.
        `schedule` - the power schedule to apply.
        """

        self.seeds = seeds
        self.mutator = mutator
        self.schedule = schedule
        self.inputs: List[str] = []
        self.reset()

    def reset(self) -> None:
        """Reset the initial population and seed index"""
        self.population = list(map(lambda x: Seed(x), self.seeds))
        #print("population",self.population)
        self.seed_index = 0

    def create_candidate(self) -> str:
        """Returns an input generated by fuzzing a seed in the population"""
        seed = self.schedule.choose(self.population)
        candidate = seed
        energy = seed.energy  
        trials = min(len(seed.data), 1 << random.randint(1, 5))
        for i in range(trials):
            candidate = self.mutator.mutate(candidate)
        return candidate.data

    def fuzz(self) -> str:
        if self.seed_index < len(self.seeds):
            # Still seeding
            self.inp = self.seeds[self.seed_index]
            self.seed_index += 1
        else:
            # Mutating
            self.inp = self.create_candidate()

        self.inputs.append(self.inp)
        #print(self.inp)
        return self.inp



class GreyboxFuzzer(AdvancedMutationFuzzer):
    """Coverage-guided mutational fuzzing."""

    def reset(self):
        """Reset the initial population, seed index, coverage information"""
        super().reset()
        self.coverages_seen = set()
        self.population = []  # population is filled during greybox fuzzing

    def compute_mask(self, seed ,runner: FunctionCoverageRunner):
        mask=[]
        for i in range(len(seed.data)):
          result = runner.run_function(seed.data)
          coverage=frozenset(runner.coverage())
          mask0=[]
          data=seed.data[:]
          input0=self.mutator.flip_pos_character(i,data)
          mutated_result = runner.run_function(input0)
          mutated_coverage = frozenset(runner.coverage())
          if coverage > mutated_coverage:
            mask0.append(0)
          else:
            mask0.append(1)
          input1=self.mutator.insert_pos_character(i,data)
          mutated_result = runner.run_function(input1)
          mutated_coverage = frozenset(runner.coverage())
          if coverage > mutated_coverage:
            mask0.append(0)
          else:
            mask0.append(1)

          input2=self.mutator.delete_pos_character(i,data)
          print("after deleting",input2)
          mutated_result = runner.run_function(input2)
          mutated_coverage = frozenset(runner.coverage())
          if len(coverage) > len(mutated_coverage):
            print("cannot delete ",i,"th position")
            mask0.append(0)
          else:
            print("can delete",i,"th position")
            mask0.append(1)
          mask.append(mask0)
        return mask

    def run(self, runner: FunctionCoverageRunner) -> Tuple[Any, str]:
        """Run function(inp) while tracking coverage.
           If we reach new coverage,
           add inp to population and its coverage to population_coverage
        """
        result, outcome = super().run(runner)

        new_coverage = frozenset(runner.coverage())
        if new_coverage not in self.coverages_seen:
            seed = Seed(self.inp)
            print(self.population)
            if seed.data not in self.population:
              seed.coverage = runner.coverage()
              self.coverages_seen.add(new_coverage)
              self.population.append(seed)
              path_id = getPathID(runner.coverage())
              if path_id not in self.schedule.path_frequency:
                self.schedule.path_frequency[path_id] = 1
              else:
                self.schedule.path_frequency[path_id] += 1

              seed.mask=self.compute_mask(seed,runner)
              print(self.population,seed.mask)

        return (result, outcome)

class CountingGreyboxFuzzer(GreyboxFuzzer):
    """Count how often individual paths are exercised."""

    def reset(self):
        """Reset path frequency"""
        super().reset()
        self.schedule.path_frequency = {}



    def run(self, runner: FunctionCoverageRunner) -> Tuple[Any, str]:
        """Inform scheduler about path frequency"""

        result, outcome = super().run(runner)

        #print(outcome)

        return(result, outcome)


def getPathID(coverage: Any) -> str:
    """Returns a unique hash for the covered statements"""
    pickled = pickle.dumps(sorted(coverage))
    return hashlib.md5(pickled).hexdigest()


class AFLFastSchedule:
    """Exponential power schedule as implemented in AFL"""
    def __init__(self, exponent: float) -> None:
        self.path_frequency: Dict = {}
        self.exponent = exponent
        self.highest_coverage = set()


    def assignEnergy(self, population: Sequence[Seed]) -> None:
        for seed in population:
            current_coverage = seed.coverage  # Get the current coverage of the seed
            seed.energy= len(current_coverage)** self.exponent
            

    def normalizedEnergy(self, population: Sequence[Seed]) -> List[float]:
        """Normalize energy"""
        energy = list(map(lambda seed: seed.energy, population))
        sum_energy = sum(energy)  # Add up all values in energy
        assert sum_energy != 0
        norm_energy = list(map(lambda nrg: nrg / sum_energy, energy))
        return norm_energy

    def choose(self, population: Sequence[Seed]) -> Seed:
        """Choose weighted by normalized energy."""
        
        self.assignEnergy(population)
        norm_energy = self.normalizedEnergy(population)
        #print(norm_energy)
        seed: Seed = random.choices(population, weights=norm_energy)[0]
        return seed

from fuzzingbook import Coverage as cv
from fuzzingbook import MutationFuzzer as mf
class MyCoverage(cv.Coverage):
  def coverage(self) -> Set[Tuple[str, int]]:
        """
        Returns the set of executed lines as (file_name, line_number) pairs
        """
        coverage_set = set()
        for file_name, line_number in self.trace():
            coverage_set.add((file_name, line_number))
        return coverage_set

class MyFunctionCoverageRunner(mf.FunctionRunner):
  def run_function(self, inp: str) -> Any:
    with MyCoverage() as cov:
      try:
        result = super().run_function(inp)
      except Exception as exc:
        self._coverage = cov.coverage()
        #raise exc
    self._coverage = cov.coverage()
    return result
  def coverage(self) -> Set[cv.Location]:
    return self._coverage

n = 999999999999
seed_input = get_initial_corpus()
fast_schedule = AFLFastSchedule(5)
fast_fuzzer = CountingGreyboxFuzzer(seed_input, Mutator(), fast_schedule)
line_runner = MyFunctionCoverageRunner(entrypoint)
start = time.time()
fast_fuzzer.runs(line_runner, trials=n)
end = time.time()

_, greybox_coverage = population_coverage(fast_fuzzer.inputs, entrypoint)
line_fast, = plt.plot(greybox_coverage, label="Boosted Greybox Fuzzer")
plt.legend(handles=[line_fast])
plt.title('Coverage over time')
plt.xlabel('# of inputs')
plt.ylabel('lines covered')
plt.show()
