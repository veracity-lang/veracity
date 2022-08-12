void busy(int fuel) {
    while (fuel > 0) { fuel = fuel - 1; }
    return;
}

int main(int argc, string[] argv) {
    int n = int_of_string(argv[1]);

    hashtable[int, bool] s = new hashtable[int, bool];

    commute {
      { for (int i = n - 1; i > 0; i = i - 2;) {
            s[i] = true;
        }
      } {
        for (int i = 3; i < n; i = i + 3;) {
            s[i] = true;
        }
      } {
        for (int i = 5; i < n; i = i + 5;) {
            s[i] = true;
        }
      }
    }

    int total = 0;

    commute {
        {
            for (int i = 0; i < n / 2; i = i + 1;) {
                total = total + ((s[i] == true) ? 1 : 0);
            }
        } {
            for (int i = n / 2; i < n; i = i + 1;) {
                total = total + ((s[i] == true) ? 1 : 0);
            }
        }
    }

    return total;
}