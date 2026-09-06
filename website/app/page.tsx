import ResearchEssay from '@/components/research-essay';
// GitHub Pages serves the same static document for every query string.
// ResearchEssay restores ?path= in the browser and on history navigation.
export default function Home() {
  return <ResearchEssay initialPath="curious" />;
}
