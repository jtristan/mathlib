set -e
set -x

remote_name=origin-bot
branch_name=nolints
owner_name=leanprover-community

# Exit if the branch already exists
git fetch $remote_name
git rev-parse --verify --quiet refs/remotes/$remote_name/$branch_name && exit 0

# Exit if there are no changes
git diff-index --quiet HEAD -- scripts/nolints.txt && exit 0

pr_title='chore(scripts): update nolints.txt'
pr_body='I am happy to remove some nolints for you!'

git checkout -b $branch_name
git add scripts/nolints.txt scripts/nolints_core.txt
git commit -m "$pr_title"

gh_api() {
  local url="$1"
  shift
  curl -s -H "Authorization: token $DEPLOY_NIGHTLY_GITHUB_TOKEN" \
    "https://api.github.com/$url" "$@"
}

git push origin-bot HEAD:$branch_name

pr_id=$(gh_api repos/$owner_name/mathlib/pulls -X POST -d @- <<EOF | jq -r .number
{
  "title": "$pr_title",
  "head": "$branch_name",
  "base": "master",
  "body": "$pr_body"
}
EOF
)

gh_api repos/$owner_name/mathlib/issues/$pr_id/comments -X POST -d @- <<EOF
{ "body": "bors r+" }
EOF

git checkout master
