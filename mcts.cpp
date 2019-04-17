#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <cassert>
#include <ctime>
#include <cstring>
#include <random>
#include "jsoncpp/json.h"

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::max;
using std::min;
using std::swap;
using std::stack;
using std::set;
using std::vector;
using std::pair;

clock_t startTime;
string debug;

namespace TankGame {
    using std::min;
    using std::max;
    using std::list;
    using std::vector;
    using std::deque;
    using std::pair;
    using std::make_pair;
    using std::stack;
    using std::set;
    using std::istream;

    enum GameResult {
        NotFinished = -2,
        Draw = -1,
        Blue = 0,
        Red = 1
    };

    enum FieldItem {
        None = 0,
        Brick = 1,
        Steel = 2,
        Base = 4,
        Blue0 = 8,
        Blue1 = 16,
        Red0 = 32,
        Red1 = 64
    };

    template<typename T>
    inline T operator~(T a) { return (T) ~(int) a; }

    template<typename T>
    inline T operator|(T a, T b) { return (T) ((int) a | (int) b); }

    template<typename T>
    inline T operator&(T a, T b) { return (T) ((int) a & (int) b); }

    template<typename T>
    inline T operator^(T a, T b) { return (T) ((int) a ^ (int) b); }

    template<typename T>
    inline T &operator|=(T &a, T b) { return (T &) ((int &) a |= (int) b); }

    template<typename T>
    inline T &operator&=(T &a, T b) { return (T &) ((int &) a &= (int) b); }

    template<typename T>
    inline T &operator^=(T &a, T b) { return (T &) ((int &) a ^= (int) b); }

    enum Action {
        Invalid = -2,
        Stay = -1,
        Up, Right, Down, Left,
        UpShoot, RightShoot, DownShoot, LeftShoot
    };

    // 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
    // Side（对战双方） - 0 为蓝，1 为红
    // Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
    // Turn（回合编号） - 从 1 开始

    const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

    // 基地的横坐标
    const int baseX[sideCount] = {fieldWidth / 2, fieldWidth / 2};

    // 基地的纵坐标
    const int baseY[sideCount] = {0, fieldHeight - 1};

    const int dx[4] = {0, 1, 0, -1}, dy[4] = {-1, 0, 1, 0};
    const FieldItem tankItemTypes[sideCount][tankPerSide] = {
            {Blue0, Blue1},
            {Red0,  Red1}
    };

    inline bool ActionIsMove(Action x) {
        return x >= Up && x <= Left;
    }

    inline bool ActionIsShoot(Action x) {
        return x >= UpShoot && x <= LeftShoot;
    }

    inline bool ActionDirectionIsOpposite(Action a, Action b) {
        return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
    }

    inline bool CoordValid(int x, int y) {
        return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
    }

    // 判断 item 是不是叠在一起的多个坦克
    inline bool HasMultipleTank(FieldItem item) {
        // 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
        // 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
        return !!(item & (item - 1));
    }

    inline int GetTankSide(FieldItem item) {
        return item == Blue0 || item == Blue1 ? Blue : Red;
    }

    inline int GetTankID(FieldItem item) {
        return item == Blue0 || item == Red0 ? 0 : 1;
    }

    // 获得动作的方向
    inline int ExtractDirectionFromAction(Action x) {
        if (x >= Up)
            return x % 4;
        return -1;
    }

    // 物件消失的记录，用于回退
    struct DisappearLog {
        FieldItem item;

        // 导致其消失的回合的编号
        int turn;

        int x, y;

        bool operator<(const DisappearLog &b) const {
            if (x == b.x) {
                if (y == b.y)
                    return item < b.item;
                return y < b.y;
            }
            return x < b.x;
        }
    };

    namespace Utility {

        pair<int, int> q[fieldHeight * fieldWidth];
        int head, tail;

        void BFSDistance(int x, int y, FieldItem (*gameField)[fieldWidth], int (*dis)[fieldWidth]) {
            for (int i = 0; i < fieldHeight; ++i)for (int j = 0; j < fieldWidth; ++j)dis[i][j] = (int) 1e9;
            dis[y][x] = 0;
            head = 0;
            tail = 0;
            q[tail++] = make_pair(x, y);
            while (head < tail) {
                auto[tx, ty]=q[head];
                int d = dis[ty][tx];
                for (int i = head; i < tail; ++i) {
                    auto p = q[i];
                    if (dis[p.second][p.first] > d)break;
                    for (int o = 0; o < 4; ++o) {
                        int nx = p.first + dx[o];
                        int ny = p.second + dy[o];
                        if (CoordValid(nx, ny) && (gameField[ny][nx] & 3) == 0 && dis[ny][nx] == (int) 1e9) {
                            dis[ny][nx] = d + 1;
                            if (gameField[ny][nx] != Base)q[tail++] = make_pair(nx, ny);
                        }
                    }
                }
                while (head < tail) {
                    auto[ttx, tty]=q[head];
                    if (dis[tty][ttx] > d)break;
                    ++head;
                    for (int o = 0; o < 4; ++o) {
                        int nx = ttx + dx[o];
                        int ny = tty + dy[o];
                        if (CoordValid(nx, ny) && (gameField[ny][nx] & 6) == 0 && (gameField[ny][nx] & 1) != 0 &&
                            dis[ny][nx] == (int) 1e9) {
                            dis[ny][nx] = d + 2;
                            q[tail++] = make_pair(nx, ny);
                        }
                    }
                }
            }
        }


        void BFSBestPath(int baseY, FieldItem (*gameField)[fieldWidth], int (*dis)[fieldWidth],
                         bool (*goodPath)[fieldWidth], bool (*goodDir)[fieldHeight][4]) {
            memset(goodDir, 0, sizeof(&goodDir));
            head = 0;
            tail = 0;
            for (int tx = 0; tx < fieldWidth; ++tx)if (goodPath[baseY][tx])q[tail++] = make_pair(tx, baseY);
            while (head < tail) {
                auto[x, y]=q[head++];
                for (int o = 0; o < 4; ++o) {
                    int nx = x - dx[o];
                    int ny = y - dy[o];
                    if (CoordValid(nx, ny) && !goodPath[ny][nx] &&
                        dis[y][x] - dis[ny][nx] == ((gameField[y][x] & 1) ? 2 : 1)) {
                        goodPath[ny][nx] = true;
                        goodDir[ny][nx][o] = true;
                        q[tail++] = make_pair(nx, ny);
                    }
                }
            }
        }

        bool vis[fieldHeight][fieldWidth];

        void dfs(int x1, int y1, FieldItem (*gameField)[fieldWidth]) {
            vis[y1][x1] = true;
            for (int i = 0; i < 4; ++i) {
                int x = x1 + dx[i], y = y1 + dy[i];
                if (CoordValid(x, y) && !vis[y][x] && (gameField[y][x] & 7) == 0) {
                    dfs(x, y, gameField);
                }
            }
        }

        bool IsLink(int x1, int y1, int x2, int y2, FieldItem (*gameField)[fieldWidth]) {
            if (x1 == -1 || x2 == -1)return false;
            memset(vis, 0, sizeof(vis));
            if (gameField[y1][x1] & 7)return 0;
            dfs(x1, y1, gameField);
            return vis[y2][x2];
        }
    }

    class TankField {
    public:
        //!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

        // 游戏场地上的物件（一个格子上可能有多个坦克）
        FieldItem gameField[fieldHeight][fieldWidth] = {};

        // 坦克是否存活
        bool tankAlive[sideCount][tankPerSide] = {{true, true},
                                                  {true, true}};

        // 基地是否存活
        bool baseAlive[sideCount] = {true, true};

        // 坦克横坐标，-1表示坦克已炸
        int tankX[sideCount][tankPerSide] = {
                {fieldWidth / 2 - 2, fieldWidth / 2 + 2},
                {fieldWidth / 2 + 2, fieldWidth / 2 - 2}
        };

        // 坦克纵坐标，-1表示坦克已炸
        int tankY[sideCount][tankPerSide] = {{0,               0},
                                             {fieldHeight - 1, fieldHeight - 1}};

        // 当前回合编号
        int currentTurn = 1;

        // 我是哪一方
        int mySide;

        // 用于回退的log
        stack<DisappearLog> logs;

        // 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
        Action previousActions[101][sideCount][tankPerSide] = {{{Stay, Stay}, {Stay, Stay}}};

        //!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

        // 本回合双方即将执行的动作，需要手动填入
        Action nextAction[sideCount][tankPerSide] = {{Invalid, Invalid},
                                                     {Invalid, Invalid}};

        // 判断行为是否合法（出界或移动到非空格子算作非法）
        // 未考虑坦克是否存活
        bool ActionIsValid(int side, int tank, Action act) {
            if (act == Invalid)
                return false;
            if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
                return false;
            if (act == Stay || act > Left)
                return true;
            int x = tankX[side][tank] + dx[act],
                    y = tankY[side][tank] + dy[act];
            return CoordValid(x, y) && gameField[y][x] == None;
        }

        // 判断 nextAction 中的所有行为是否都合法
        // 忽略掉未存活的坦克
        bool ActionIsValid() {
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
                        return false;
            return true;
        }

    private:
        void _destroyTank(int side, int tank) {
            tankAlive[side][tank] = false;
            tankX[side][tank] = tankY[side][tank] = -1;
        }

        void _revertTank(int side, int tank, DisappearLog &log) {
            int &currX = tankX[side][tank], &currY = tankY[side][tank];
            if (tankAlive[side][tank])
                gameField[currY][currX] &= ~tankItemTypes[side][tank];
            else
                tankAlive[side][tank] = true;
            currX = log.x;
            currY = log.y;
            gameField[currY][currX] |= tankItemTypes[side][tank];
        }

    public:

        // 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
        bool DoAction() {
            ++cnt;
            if (!ActionIsValid())
                return false;

            // 1 移动
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++) {
                    Action act = nextAction[side][tank];

                    // 保存动作
                    previousActions[currentTurn][side][tank] = act;
                    if (tankAlive[side][tank] && ActionIsMove(act)) {
                        int &x = tankX[side][tank], &y = tankY[side][tank];
                        FieldItem &items = gameField[y][x];

                        // 记录 Log
                        DisappearLog log;
                        log.x = x;
                        log.y = y;
                        log.item = tankItemTypes[side][tank];
                        log.turn = currentTurn;
                        logs.push(log);

                        // 变更坐标
                        x += dx[act];
                        y += dy[act];

                        // 更换标记（注意格子可能有多个坦克）
                        gameField[y][x] |= log.item;
                        items &= ~log.item;
                    }
                }

            // 2 射♂击
            set<DisappearLog> itemsToBeDestroyed;
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++) {
                    Action act = nextAction[side][tank];
                    if (tankAlive[side][tank] && ActionIsShoot(act)) {
                        int dir = ExtractDirectionFromAction(act);
                        int x = tankX[side][tank], y = tankY[side][tank];
                        bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
                        while (true) {
                            x += dx[dir];
                            y += dy[dir];
                            if (!CoordValid(x, y))
                                break;
                            FieldItem items = gameField[y][x];
                            if (items != None) {
                                // 对射判断
                                if (items >= Blue0 &&
                                    !hasMultipleTankWithMe && !HasMultipleTank(items)) {
                                    // 自己这里和射到的目标格子都只有一个坦克
                                    Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
                                    if (ActionIsShoot(theirAction) &&
                                        ActionDirectionIsOpposite(act, theirAction)) {
                                        // 而且我方和对方的射击方向是反的
                                        // 那么就忽视这次射击
                                        break;
                                    }
                                }

                                // 标记这些物件要被摧毁了（防止重复摧毁）
                                for (int mask = 1; mask <= Red1; mask <<= 1)
                                    if (items & mask) {
                                        DisappearLog log;
                                        log.x = x;
                                        log.y = y;
                                        log.item = (FieldItem) mask;
                                        log.turn = currentTurn;
                                        itemsToBeDestroyed.insert(log);
                                    }
                                break;
                            }
                        }
                    }
                }

            for (auto &log : itemsToBeDestroyed) {
                switch (log.item) {
                    case Base: {
                        int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                        baseAlive[side] = false;
                        break;
                    }
                    case Blue0:
                        _destroyTank(Blue, 0);
                        break;
                    case Blue1:
                        _destroyTank(Blue, 1);
                        break;
                    case Red0:
                        _destroyTank(Red, 0);
                        break;
                    case Red1:
                        _destroyTank(Red, 1);
                        break;
                    case Steel:
                        continue;
                    default:;
                }
                gameField[log.y][log.x] &= ~log.item;
                logs.push(log);
            }

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    nextAction[side][tank] = Invalid;

            currentTurn++;
            return true;
        }

        // 回到上一回合
        bool Revert() {
            if (currentTurn == 1)
                return false;

            currentTurn--;
            while (!logs.empty()) {
                DisappearLog &log = logs.top();
                if (log.turn == currentTurn) {
                    logs.pop();
                    switch (log.item) {
                        case Base: {
                            int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                            baseAlive[side] = true;
                            gameField[log.y][log.x] = Base;
                            break;
                        }
                        case Brick:
                            gameField[log.y][log.x] = Brick;
                            break;
                        case Blue0:
                            _revertTank(Blue, 0, log);
                            break;
                        case Blue1:
                            _revertTank(Blue, 1, log);
                            break;
                        case Red0:
                            _revertTank(Red, 0, log);
                            break;
                        case Red1:
                            _revertTank(Red, 1, log);
                            break;
                        default:;
                    }
                } else
                    break;
            }
            return true;
        }

        // 游戏是否结束？谁赢了？
        GameResult GetGameResult() {
            bool fail[sideCount] = {};
            for (int side = 0; side < sideCount; side++)
                if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
                    fail[side] = true;
            if (fail[0] == fail[1])
                return fail[0] || currentTurn > 100 ? Draw : NotFinished;
            if (fail[Blue])
                return Red;
            return Blue;
        }

        GameResult GetGameResult(int side, int tank) {
            bool fail[sideCount] = {};
            fail[side] = !baseAlive[side] || !tankAlive[side][tank];
            fail[!side] = !baseAlive[!side] || !tankAlive[!side][!tank];
            if (fail[0] == fail[1])
                return fail[0] || currentTurn > 100 ? Draw : NotFinished;
            if (fail[Blue])
                return Red;
            return Blue;
        }

        // 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
        TankField(int hasBrick[3], int mySide) : mySide(mySide) {
            for (int i = 0; i < 3; i++) {
                int mask = 1;
                for (int y = i * 3; y < (i + 1) * 3; y++) {
                    for (int x = 0; x < fieldWidth; x++) {
                        if (hasBrick[i] & mask)
                            gameField[y][x] = Brick;
                        mask <<= 1;
                    }
                }
            }
            for (int side = 0; side < sideCount; side++) {
                for (int tank = 0; tank < tankPerSide; tank++)
                    gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
                gameField[baseY[side]][baseX[side]] = Base;
            }
            gameField[baseY[0] + 1][baseX[0]] = gameField[baseY[1] - 1][baseX[1]] = Steel;
        }

        // 打印场地
        void DebugPrint() {
#ifndef _BOTZONE_ONLINE
            const string side2String[] = {"蓝", "红"};
            const string boolean2String[] = {"已炸", "存活"};
            const char *boldHR = "==============================";
            const char *slimHR = "------------------------------";
            cout << boldHR << endl
                 << "图例：" << endl
                 << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
                 << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1" << endl
                 << slimHR << endl;
            for (int y = 0; y < fieldHeight; y++) {
                for (int x = 0; x < fieldWidth; x++) {
                    switch (gameField[y][x]) {
                        case None:
                            cout << '.';
                            break;
                        case Brick:
                            cout << '#';
                            break;
                        case Steel:
                            cout << '%';
                            break;
                        case Base:
                            cout << '*';
                            break;
                        case Blue0:
                            cout << 'b';
                            break;
                        case Blue1:
                            cout << 'B';
                            break;
                        case Red0:
                            cout << 'r';
                            break;
                        case Red1:
                            cout << 'R';
                            break;
                        default:
                            cout << '@';
                            break;
                    }
                }
                cout << endl;
            }
            cout << slimHR << endl;
            for (int side = 0; side < sideCount; side++) {
                cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
                for (int tank = 0; tank < tankPerSide; tank++)
                    cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
                cout << endl;
            }
            cout << "当前回合：" << currentTurn << "，";
            GameResult result = GetGameResult();
            if (result == -2)
                cout << "游戏尚未结束" << endl;
            else if (result == -1)
                cout << "游戏平局" << endl;
            else
                cout << side2String[result] << "方胜利" << endl;
            cout << boldHR << endl;
#endif
        }

        bool JustShoot(int side, int tank) {
            return previousActions[currentTurn - 1][side][tank] > Left;
        }

        bool CanShootEachOther(int x1, int y1, int x2, int y2) {
            if (x1 == x2) {
                if (y1 > y2)std::swap(y1, y2);
                for (int i = y1 + 1; i < y2; ++i)if (gameField[i][x1] & 7)return false;
                return true;
            } else if (y1 == y2) {
                if (x1 > x2)std::swap(x1, x2);
                for (int i = x1 + 1; i < x2; ++i)if (gameField[y1][i] & 7)return false;
                return true;
            }
            return false;
        }

        bool CanTankShootEachOther(int side, int tank) {
            if (!tankAlive[side][tank] || !tankAlive[!side][!tank])return false;
            return CanShootEachOther(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]);
        }

        bool IsLink(int x1, int y1, int x2, int y2) {
            return Utility::IsLink(x1, y1, x2, y2, gameField);
        }

        int dis[sideCount][tankPerSide][fieldHeight][fieldWidth]{0};
        int attackDis[sideCount][tankPerSide]{0};
        bool goodPath[sideCount][tankPerSide][fieldHeight][fieldWidth]{false};
        bool goodDir[sideCount][tankPerSide][fieldHeight][fieldWidth][4]{false};

        void InitDistance(int side, int tank) {
            Utility::BFSDistance(tankX[side][tank], tankY[side][tank], gameField, dis[side][tank]);
            int ret = (int) 1e9;
            for (int tx = baseX[!side] + 1, det = 0; tx < fieldWidth; ++tx) {
                if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                if (gameField[baseY[!side]][tx] & 1)det += 2;
            }
            for (int tx = baseX[!side] - 1, det = 0; tx >= 0; --tx) {
                if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                if (gameField[baseY[!side]][tx] & 1)det += 2;
            }
            ++ret;
            attackDis[side][tank] = ret;
            for (int i = 0; i < fieldHeight; ++i)for (int j = 0; j < fieldWidth; ++j)goodPath[side][tank][i][j] = false;
            for (int tx = baseX[!side] + 1, det = 0; tx < fieldWidth; ++tx) {
                if (dis[side][tank][baseY[!side]][tx] + det == ret)goodPath[side][tank][baseY[!side]][tx] = true;
                if (gameField[baseY[!side]][tx] & 1)det += 2;
            }
            for (int tx = baseX[!side] - 1, det = 0; tx >= 0; --tx) {
                if (dis[side][tank][baseY[!side]][tx] + det == ret)goodPath[side][tank][baseY[!side]][tx] = true;
                if (gameField[baseY[!side]][tx] & 1)det += 2;
            }
            Utility::BFSBestPath(baseY[!side], gameField, dis[side][tank], goodPath[side][tank], goodDir[side][tank]);
        }

        bool Defensible(int side, int tank) {
            if (!tankAlive[side][tank])return false;
            if (!tankAlive[!side][!tank])return true;
            InitDistance(side, tank);
            InitDistance(!side, !tank);
            if (tankX[side][tank] <= fieldWidth / 2) {
                for (int x = baseX[side] - 1, det = 0, mn = (int) 1e9; x >= 0; --x) {
                    if (mn > dis[!side][!tank][baseY[side]][x] + det &&
                        dis[side][tank][baseY[side]][x] >= dis[!side][!tank][baseY[side]][x])
                        return false;
                    mn = min(mn, dis[side][tank][baseY[side]][x]);
                    if (gameField[baseY[!side]][x] & 1)det += 2;
                }
            } else {
                for (int x = baseX[side] + 1, det = 0, mn = (int) 1e9; x <= fieldWidth; ++x) {
                    if (mn > dis[!side][!tank][baseY[side]][x] + det &&
                        dis[side][tank][baseY[side]][x] >= dis[!side][!tank][baseY[side]][x])
                        return false;
                    mn = min(mn, dis[side][tank][baseY[side]][x]);
                    if (gameField[baseY[!side]][x] & 1)det += 2;
                }
            }
            return true;
        }

        int getDirection(int x1, int y1, int x2, int y2) {
            if (x1 == x2) return y1 < y2 ? 2 : 0;
            if (y1 == y2) return x1 < x2 ? 1 : 3;
            return -1;
        }

        int getDirection(int side, int tank) {
            return getDirection(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]);
        }

        int GetCorner(int side, int tank) {
            int d = getDirection(!side, !tank);
            int x = tankX[side][tank], y = tankY[side][tank];
            int ret = 0;
            while (CoordValid(x, y)) {
                for (int o = 0; o < 4; ++o) {
                    if (goodDir[side][tank][y][x][o]) {
                        int nx = x + dx[o], ny = y + dy[o];
                        if (CoordValid(nx, ny) && o != d) return ret;
                    }
                }
                ++ret;
                x += dx[d];
                y += dy[d];
            }
            return 50;
        }

        int EstimateAttack(int side, int tank) {
            if (!tankAlive[side][tank])return (int) -1e8;
            if (!tankAlive[!side][!tank])return (int) 1e8;
            InitDistance(side, tank);
            InitDistance(!side, !tank);
            if (IsLink(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank])) {
                if (dis[side][tank][baseY[side]][baseX[side]] >= dis[!side][!tank][baseY[side]][baseX[side]] &&
                    CanTankShootEachOther(side, tank)) {
                    return 10000 * (2 * (attackDis[!side][!tank] - attackDis[side][tank]) +
                                    (GetCorner(!side, !tank) - GetCorner(side, tank)));
                } else {
                    return 10000 * 2 * (attackDis[!side][!tank] - attackDis[side][tank]);
                }
            } else {
                return 2 * attackDis[!side][!tank] - 2 * attackDis[side][tank];
            }
        }

        int EstimateAction(int side, int tank, Action act) {
            nextAction[side][tank] = act;
            nextAction[side][!tank] = Stay;
            nextAction[!side][tank] = Stay;
            nextAction[!side][!tank] = Stay;
            DoAction();
            int ret = EstimateAttack(side, tank);
            Revert();
            return ret;
        }
    };

    TankField *field;

    // 内部函数
    namespace Internals {
        Json::Reader reader;
#ifdef _BOTZONE_ONLINE
        Json::FastWriter writer;
#else
        Json::StyledWriter writer;
#endif

        void _processRequestOrResponse(Json::Value &value, bool isOpponent) {
            if (value.isArray()) {
                if (!isOpponent) {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[field->mySide][tank] = (Action) value[tank].asInt();
                } else {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[1 - field->mySide][tank] = (Action) value[tank].asInt();
                    field->DoAction();
                }
            } else {
                // 是第一回合，裁判在介绍场地
                int hasBrick[3];
                for (int i = 0; i < 3; i++)
                    hasBrick[i] = value["field"][i].asInt();
                field = new TankField(hasBrick, value["mySide"].asInt());
            }
        }

        // 请使用 SubmitAndExit 或者 SubmitAndDontExit
        void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "") {
            Json::Value output(Json::objectValue), response(Json::arrayValue);
            response[0U] = tank0;
            response[1U] = tank1;
            output["response"] = response;
            if (!debug.empty())
                output["debug"] = debug;
            if (!data.empty())
                output["data"] = data;
            if (!globalData.empty())
                output["globalData"] = globalData;
            cout << writer.write(output) << endl;
        }
    }

    // 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
    // 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
    void ReadInput(istream &in, string &outData, string &outGlobalData) {
        Json::Value input;
        string inputString;
        do {
            getline(in, inputString);
        } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
        // 猜测是单行还是多行
        char lastChar = inputString[inputString.size() - 1];
        if (lastChar != '}' && lastChar != ']') {
            // 第一行不以}或]结尾，猜测是多行
            string newString;
            do {
                getline(in, newString);
                inputString += newString;
            } while (newString != "}" && newString != "]");
        }
#endif
        Internals::reader.parse(inputString, input);

        if (input.isObject()) {
            Json::Value requests = input["requests"], responses = input["responses"];
            if (!requests.isNull() && requests.isArray()) {
                int i, n = requests.size();
                for (i = 0; i < n; i++) {
                    Internals::_processRequestOrResponse(requests[i], true);
                    if (i < n - 1)
                        Internals::_processRequestOrResponse(responses[i], false);
                }
                outData = input["data"].asString();
                outGlobalData = input["globaldata"].asString();
                return;
            }
        }
        Internals::_processRequestOrResponse(input, true);
    }

    // 提交决策并退出，下回合时会重新运行程序
    void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "") {
        Internals::_submitAction(tank0, tank1, debug, data, globalData);
#ifndef _BOTZONE_ONLINE
        std::cerr << (clock() - startTime) * 1.0 / CLOCKS_PER_SEC << endl;
        std::cerr << cnt << endl;
#endif
        exit(0);
    }

    // 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
    // 如果游戏结束，程序会被系统杀死
    void SubmitAndDontExit(Action tank0, Action tank1) {
        Internals::_submitAction(tank0, tank1);
        field->nextAction[field->mySide][0] = tank0;
        field->nextAction[field->mySide][1] = tank1;
        cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
    }

    int RandBetween(int from, int to) {
        return rand() % (to - from) + from;
    }

    std::random_device rd;
    std::default_random_engine gen(rd());

    // 决策树
    /* 两种节点，分别为决策节点和状态节点
     * 每个状态节点与一个局面对应，每个状态节点有若干个儿子决策节点，且分为两类，代表双方的决策
     * 在两类节点中各取一个，它们有一个共同的儿子状态节点，代表上一状态双方选择这两个决策后到达的局面
     */

    struct DecisonTree {
        struct StateNode;
        struct ChoiceNode;
        static constexpr double C = 2;
        int side, tank;

        Action RandAction(int side, int tank) {
            int w[9]{0};
            for (int i = 0; i < 9; ++i)
                if (field->ActionIsValid(side, tank, (TankGame::Action) (i - 1)))
                    w[i] = field->EstimateAction(side, tank, (TankGame::Action) (i - 1));
            std::discrete_distribution<> d(w, w + 9);
            return (TankGame::Action) (d(gen) - 1);
//            while (true) {
//                auto act = (TankGame::Action) RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
//                if (field->ActionIsValid(side, tank, act))
//                    return act;
//            }
        }

        struct ChoiceNode {
            StateNode *fa;
            vector<StateNode *> son;
            TankGame::Action act[2];
            int quality, times;

            ChoiceNode() : fa(nullptr), quality(0), times(0), act{TankGame::Invalid} {}
        };

        const int maxDepth = 30;

        struct StateNode {
            ChoiceNode *fa[sideCount];
            vector<ChoiceNode *> son[2];
            int times;
            bool isExpanded;

            StateNode() : times(0), fa{nullptr}, isExpanded(false) {}

            double CalcScore(ChoiceNode *p, int side) {
                if (p->times == 0)
                    return 1e7 +
                           1.0 * field->EstimateAction(side, 0, p->act[0]) * field->EstimateAction(side, 1, p->act[1]);
                return 1.0 * p->quality / p->times + C * sqrt(log(times) / p->times);
            }

            TankGame::GameResult Work(int depth) {
                if (depth > maxDepth)return TankGame::Draw;
                if (field->GetGameResult() != TankGame::NotFinished)return field->GetGameResult();
                if (tankPerSide == 1 && !field->tankAlive[field->mySide][field->mySide ^ tankSide])
                    return (TankGame::GameResult) !field->mySide;
                if (tankPerSide == 1 && !field->tankAlive[!field->mySide][!field->mySide ^ tankSide])
                    return (TankGame::GameResult) field->mySide;
                if (!isExpanded) {
                    isExpanded = true;
                    for (int side = 0; side < sideCount; ++side) {
                        if (tankPerSide == 1) {
                            for (int i = TankGame::Stay; i <= TankGame::LeftShoot; ++i) {
                                auto act = (TankGame::Action) i;
                                if (field->ActionIsValid(side, tankSide ^ side, act)) {
                                    auto newChoice = new ChoiceNode();
                                    newChoice->fa = this;
                                    newChoice->act[0] = act;
                                    son[side].push_back(newChoice);
                                }
                            }
                        } else {
                            for (int i = TankGame::Stay; i <= TankGame::LeftShoot; ++i) {
                                auto act0 = (TankGame::Action) i;
                                if (!field->tankAlive[side][0] && act0 != TankGame::Stay)break;
                                if (field->ActionIsValid(side, 0, act0)) {
                                    for (int j = TankGame::Stay; j <= TankGame::LeftShoot; ++j) {
                                        auto act1 = (TankGame::Action) j;
                                        if (!field->tankAlive[side][1] && act1 != TankGame::Stay)break;
                                        if (field->ActionIsValid(side, 1, act1)) {
                                            auto newChoice = new ChoiceNode();
                                            newChoice->fa = this;
                                            newChoice->act[0] = act0;
                                            newChoice->act[1] = act1;
                                            son[side].push_back(newChoice);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    return Simulate(depth);
                }
                return Select(depth);
            }

            TankGame::GameResult Select(int depth) {
                if (depth > maxDepth)return TankGame::Draw;
                times += 2;
                double mx = -1e9;
                ChoiceNode *myChoice = nullptr;
                for (auto c:son[field->mySide]) {
                    double tmp = CalcScore(c, field->mySide);
                    if (tmp > mx) {
                        mx = tmp;
                        myChoice = c;
                    }
                }
                mx = -1e9;
                ChoiceNode *enemyChoice = nullptr;
                for (auto c:son[!field->mySide]) {
                    double tmp = CalcScore(c, !field->mySide);
                    if (tmp > mx) {
                        mx = tmp;
                        enemyChoice = c;
                    }
                }
                assert(myChoice != nullptr);
                assert(enemyChoice != nullptr);
                if (tankPerSide == 1) {
                    field->nextAction[field->mySide][tankSide ^ field->mySide] = myChoice->act[0];
                    field->nextAction[!field->mySide][!tankSide ^ field->mySide] = enemyChoice->act[0];
                    field->nextAction[field->mySide][!tankSide ^ field->mySide] = TankGame::Stay;
                    field->nextAction[!field->mySide][tankSide ^ field->mySide] = TankGame::Stay;
                } else {
                    field->nextAction[field->mySide][0] = myChoice->act[0];
                    field->nextAction[field->mySide][1] = myChoice->act[1];
                    field->nextAction[!field->mySide][0] = enemyChoice->act[0];
                    field->nextAction[!field->mySide][1] = enemyChoice->act[1];
                }
                assert(field->DoAction());
                TankGame::GameResult result = TankGame::NotFinished;
                for (auto s:myChoice->son) {
                    if (s->fa[!field->mySide] == enemyChoice) {
                        result = s->Work(depth + 1);
                    }
                }
                if (result == TankGame::NotFinished) {
                    auto *newState = new StateNode();
                    newState->fa[field->mySide] = myChoice;
                    newState->fa[!field->mySide] = enemyChoice;
                    myChoice->son.push_back(newState);
                    enemyChoice->son.push_back(newState);
                    result = newState->Work(depth + 1);
                }
                field->Revert();
                myChoice->times += 2;
                enemyChoice->times += 2;
                if (result == TankGame::Draw) {
                    myChoice->quality += 1;
                    enemyChoice->quality += 1;
                } else if (result == field->mySide)myChoice->quality += 2;
                else enemyChoice->quality += 2;
                return result;
            }

            TankGame::GameResult Simulate(int depth) {
                if (depth > maxDepth)return TankGame::Draw;
                if (tankPerSide == 1) {
                    field->nextAction[field->mySide][tankSide ^ field->mySide] = RandAction(field->mySide,
                                                                                            tankSide ^ field->mySide);
                    field->nextAction[!field->mySide][!tankSide ^ field->mySide] = RandAction(!field->mySide,
                                                                                              !tankSide ^
                                                                                              field->mySide);
                    field->nextAction[field->mySide][!tankSide ^ field->mySide] = TankGame::Stay;
                    field->nextAction[!field->mySide][tankSide ^ field->mySide] = TankGame::Stay;
                } else {
                    for (int i = 0; i < 2; ++i)for (int j = 0; j < 2; ++j)field->nextAction[i][j] = RandAction(i, j);
                }
                assert(field->DoAction());
                TankGame::GameResult result;
                if (field->GetGameResult() != TankGame::NotFinished)result = field->GetGameResult();
                else if (!field->tankAlive[field->mySide][0] || !field->tankAlive[field->mySide][1])
                    result = (TankGame::GameResult) !field->mySide;
                else if (!field->tankAlive[!field->mySide][0] || !field->tankAlive[!field->mySide][1])
                    result = (TankGame::GameResult) field->mySide;
                else result = Simulate(depth + 1);
                field->Revert();
                return result;
            }
        };

        StateNode *root;
        ChoiceNode *bestChoice;

        void MCTS(clock_t countDown) {
            int cnt = 0;
            while (clock() < countDown) {
                root->Work(0);
                ++cnt;
            }
            bestChoice = nullptr;
            for (auto c:root->son[field->mySide]) {
                if (bestChoice == nullptr || c->times > bestChoice->times) {
                    bestChoice = c;
                }
            }
#ifndef _BOTZONE_ONLINE
            std::cerr << cnt << endl;
            std::cerr << bestChoice->times << endl;
#endif
        }

        TankGame::Action GetAction(clock_t countDown) {
            MCTS(countDown);
            assert(bestChoice != nullptr);
            root = bestChoice;
            return bestChoice->act;
        }

        DecisonTree(int tank) : tank(tank), side(TankGame::field->mySide) {
            root = new StateNode();
        }
    };
}
TankGame::DecisonTree *DT[2];

int main() {
    srand((unsigned) time(nullptr));
    while (true) {
        string data, globaldata;
        TankGame::ReadInput(cin, data, globaldata);
        TankGame::field->DebugPrint();
        startTime = clock();
        TankGame::Action act0, act1;
        if (TankGame::field->currentTurn == 1) {
            DT[0] = new TankGame::DecisonTree(0);
            DT[1] = new TankGame::DecisonTree(1);
            act0 = DT[0]->GetAction(startTime + (int) (CLOCKS_PER_SEC * 0.99));
            act1 = DT[1]->GetAction(startTime + (int) (CLOCKS_PER_SEC * 1.98));
        } else {
            act0 = DT[0]->GetAction(startTime + (int) (CLOCKS_PER_SEC * 0.49));
            act1 = DT[1]->GetAction(startTime + (int) (CLOCKS_PER_SEC * 0.98));
        }
        TankGame::SubmitAndDontExit(act0, act1);
        if (TankGame::field->currentTurn > 101)break;
    }
}