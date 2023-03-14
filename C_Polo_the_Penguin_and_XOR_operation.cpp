#include <bits/stdc++.h>
using namespace std;

int main()
{

    int n;
    cin >> n;
    vector<bool> visited(n + 1);
    vector<int> ans(n + 1);
    int mask = (1 << 20) - 1;
    for (int i = n; i >= 0; i--)
    {
        while ((mask ^ i) > n || visited[mask ^ i] == true)
        {
            mask = mask >> 1;
        }
        ans[i] = mask ^ i;
        visited[mask ^ i] = true;
    }
    long long score = n * 1LL * (n + 1);
    cout << score << endl;
    for (auto val : ans)
    {
        cout << val << " ";
    }
    cout << endl;
    return 0;
}