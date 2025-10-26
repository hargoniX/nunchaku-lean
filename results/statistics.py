import pandas
from matplotlib import pyplot as plt
import glob
from dataclasses import dataclass

PERF_DIR = "perf"
SOUND_DIR = "sound"

def analyze(df: pandas.DataFrame, name: str):
    # We want:
    # - summary of result kinds
    # - plots of sat/unsat speed
    print(f"== RESULTS for {name}")
    print(df.value_counts("result"))
    print("")

def analyze_dir(dir_name: str):
    dfs = []
    print(f"= RESULTS for {dir_name}")
    for filepath in glob.iglob(f"{dir_name}/*.csv"):
        df = pandas.read_csv(filepath)
        analyze(df, filepath)
        dfs.append(df)
    df = pandas.concat(dfs)
    analyze(df, f"{dir_name} overall")
    print("")

def main():
    analyze_dir(PERF_DIR)
    analyze_dir(SOUND_DIR)


if __name__ == "__main__":
    main()
